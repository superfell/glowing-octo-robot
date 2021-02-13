use arr_macro::arr;
use std::usize;

enum Node<T> {
    None,
    Leaf(T),
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
            match n {
                Node::None => {
                    *n = Node::Container4(Box::new(Container4::new()));
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

#[cfg(test)]
mod test {
    use super::Tree;

    #[test]
    fn container4_only() {
        let mut x = Tree::<String>::new();
        x.put(&[1, 2], String::from("alice"));
        x.put(&[1, 2, 3], String::from("bob"));
        x.put(&[2, 10, 11], String::from("eve"));

        assert_eq!(x.get(&[1, 2]), Some(&String::from("alice")));
        assert_eq!(x.get(&[1, 2, 3]), Some(&String::from("bob")));
        assert_eq!(x.get(&[2, 10, 11]), Some(&String::from("eve")));

        assert_eq!(x.get(&[5]), None);
        assert_eq!(x.get(&[]), None);
        assert_eq!(x.get(&[2, 10]), None);
        assert_eq!(x.get(&[2, 10, 11, 12]), None);
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
