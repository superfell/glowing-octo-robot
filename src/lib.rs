use arr_macro::arr;
use std::cmp::min;

enum Node<T> {
    None,
    Leaf(T),
    Path(Box<Path<T>>),
    Container4(Box<Container4<T>>),
    Container256(Box<Container256<T>>),
}

impl<T> Node<T> {
    fn leaf_value(&self) -> Option<&T> {
        match &self {
            Node::Leaf(v) => Some(v),
            Node::None => None,
            _ => panic!("A nodes value should always be a Leaf"),
        }
    }
}

impl<T> Default for Node<T> {
    fn default() -> Self {
        Node::None
    }
}

struct Path<T> {
    key: Vec<u8>,
    child: Node<T>,
}

// wrap_path_in_container returns a new container that contains the path.
fn wrap_path_in_container<T>(n: &mut Node<T>) -> Box<Container4<T>> {
    if let Node::Path(p) = n {
        let mut c = Box::new(Container4::<T> {
            keys: [p.key.remove(0), 0, 0, 0],
            children: [Node::None, Node::None, Node::None, Node::None],
            count: 1,
            value: Node::None,
        });
        // path.key might be empty now, in which case we can put the path child directly
        // into the new container rather than the remaining path
        c.children[0] = if p.key.is_empty() {
            std::mem::take(&mut p.child)
        } else {
            std::mem::take(n)
        };
        c
    } else {
        panic!("wrap_path_in_container should be called with a Node::Path");
    }
}

fn split_path_maybe<T>(n: &mut Node<T>, k: &[u8]) -> Option<Node<T>> {
    if let Node::Path(p) = n {
        // if k has a prefix of p, then we're okay, otherwise we need
        // to split this path where the common prefix ends.

        let prefixlen = common_prefix_len(k, p.key.as_slice());
        if prefixlen < p.key.len() {
            // mutate path(child) to path(container(path(child)))
            let head = p.key[..prefixlen].to_vec();
            p.key = p.key[prefixlen..].to_vec();
            let c = wrap_path_in_container(n);
            // its possible that there's no matching prefix at all.
            // In that case we can use the container we just built as the result
            // otherwise we need a path to the container
            return if head.is_empty() {
                Some(Node::Container4(c))
            } else {
                Some(Node::Path(Box::new(Path {
                    key: head,
                    child: Node::Container4(c),
                })))
            };
        }
        None
    } else {
        panic!("split_path_maybe should be called with a Node::Path");
    }
}
struct Container4<T> {
    keys: [u8; 4],
    children: [Node<T>; 4],
    count: usize,
    value: Node<T>,
}

impl<T> Container4<T> {
    fn new() -> Self {
        Container4::<T> {
            children: [Node::None, Node::None, Node::None, Node::None],
            value: Node::None,
            count: 0,
            keys: [0; 4],
        }
    }
    fn should_grow(&self, key: u8) -> bool {
        if self.count < 4 {
            return false;
        }
        matches!(self.get_child(key), Node::None)
    }
    fn get_child(&self, key: u8) -> &Node<T> {
        for i in 0..self.count {
            if self.keys[i] == key {
                return &self.children[i];
            }
        }
        &Node::None
    }
    fn get_child_slot(&mut self, key: u8) -> &mut Node<T> {
        for i in 0..self.count {
            if self.keys[i] == key {
                return &mut self.children[i];
            }
        }
        assert!(self.count < 4, "container should of been grown already");
        let idx = self.count;
        self.keys[idx] = key;
        self.count += 1;
        &mut self.children[idx]
    }
}

struct Container256<T> {
    children: [Node<T>; 256],
    value: Node<T>,
}

impl<T> Container256<T> {
    fn new(src: &mut Box<Container4<T>>) -> Container256<T> {
        let mut n = Container256 {
            children: arr![Node::None; 256],
            value: Node::None,
        };
        std::mem::swap(&mut src.value, &mut n.value);
        for i in 0..src.count {
            let x = &mut src.children[i];
            let y = &mut n.children[src.keys[i] as usize];
            std::mem::swap(x, y);
        }
        n
    }
}

pub struct Tree<T> {
    root: Node<T>,
}

impl<T: 'static> Default for Tree<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: 'static> Tree<T> {
    pub fn new() -> Self {
        Self { root: Node::None }
    }

    pub fn put(&mut self, key: &[u8], value: T) {
        let mut n = &mut self.root;
        let mut k = key;
        while !k.is_empty() {
            if let Node::Container4(c) = n {
                if c.should_grow(k[0]) {
                    *n = Node::Container256(Box::new(Container256::new(c)));
                }
            }
            if let Node::Path(_) = n {
                if let Some(new_node) = split_path_maybe(n, k) {
                    *n = new_node
                }
            }
            match n {
                Node::None => {
                    // We've reached the bottom of the tree for this branch, we can create
                    // a path + leaf to handle the remaining key
                    *n = Node::Path(Box::new(Path {
                        key: k.to_vec(),
                        child: Node::Leaf(value),
                    }));
                    return;
                }
                Node::Path(p) => {
                    // at this point p must be a prefix of k. (due to split_path_maybe call above)
                    assert!(k.starts_with(p.key.as_slice()));
                    n = &mut p.child;
                    k = &k[p.key.len()..];
                }
                Node::Leaf(_) => {
                    let mut c = Box::new(Container4::new());
                    c.value = std::mem::take(n);
                    *n = Node::Container4(c);
                }
                Node::Container4(c) => {
                    n = c.get_child_slot(k[0]);
                    k = &k[1..]
                }
                Node::Container256(c) => {
                    n = &mut c.children[k[0] as usize];
                    k = &k[1..]
                }
            }
        }
        match n {
            Node::None => {
                *n = Node::Leaf(value);
            }
            Node::Leaf(v) => {
                *v = value;
            }
            Node::Path(_) => {
                let mut c = wrap_path_in_container(n);
                c.value = Node::Leaf(value);
                *n = Node::Container4(c);
            }
            Node::Container4(c) => {
                c.value = Node::Leaf(value);
            }
            Node::Container256(c) => {
                c.value = Node::Leaf(value);
            }
        }
    }

    pub fn get(&self, key: &[u8]) -> Option<&T> {
        let mut n = &self.root;
        let mut k = key;
        loop {
            match n {
                Node::Leaf(t) => {
                    if k.is_empty() {
                        return Some(t);
                    } else {
                        return None;
                    }
                }
                Node::Path(p) => {
                    if k.len() < p.key.len() {
                        return None;
                    }
                    if p.key.as_slice() != &k[..p.key.len()] {
                        return None;
                    }
                    n = &p.child;
                    k = &k[p.key.len()..]
                }
                Node::Container4(c) => {
                    if k.is_empty() {
                        return c.value.leaf_value();
                    }
                    n = c.get_child(k[0]);
                    k = &k[1..];
                }
                Node::Container256(c) => {
                    if k.is_empty() {
                        return c.value.leaf_value();
                    }
                    n = &c.children[k[0] as usize];
                    k = &k[1..];
                }
                Node::None => return None,
            };
        }
    }
}

fn common_prefix_len(a: &[u8], b: &[u8]) -> usize {
    let len = min(a.len(), b.len());
    for i in 0..len {
        if a[i] != b[i] {
            return i;
        }
    }
    len
}

#[cfg(test)]
mod test {
    use super::Tree;

    #[test]
    fn container4_only() {
        let mut x = Tree::<String>::new();
        x.put(&[1, 2], String::from("alice"));
        x.put(&[1, 2, 3], String::from("bob"));
        x.put(&[2, 10, 11, 12, 13, 14], String::from("eve"));
        x.put(&[2, 10, 11], String::from("jim"));

        assert_eq!(x.get(&[1, 2]), Some(&String::from("alice")));
        assert_eq!(x.get(&[1, 2, 3]), Some(&String::from("bob")));
        assert_eq!(x.get(&[2, 10, 11, 12, 13, 14]), Some(&String::from("eve")));
        assert_eq!(x.get(&[2, 10, 11]), Some(&String::from("jim")));

        assert_eq!(x.get(&[5]), None);
        assert_eq!(x.get(&[]), None);
        assert_eq!(x.get(&[2, 10]), None);
        assert_eq!(x.get(&[2, 10, 11, 12]), None);
        assert_eq!(x.get(&[2, 10, 11, 12, 13, 14, 15]), None);
    }

    #[test]
    fn container4_grow_to_256() {
        let mut x = Tree::<u8>::new();
        for i in 10..50 {
            x.put(&[1, 2, 3, i], i);
        }
        for i in 10..50 {
            assert_eq!(x.get(&[1, 2, 3, i]), Some(&i));
        }
    }
}
