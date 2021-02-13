use arr_macro::arr;
use std::usize;

trait Container<T> {
    fn get_value(&self) -> Option<&T>;
    fn get_value_slot(&mut self) -> &mut Node<T>;
    fn set_value(&mut self, v: Node<T>);

    fn get_keys(&self) -> Vec<u8>;
    fn get_child(&self, key: u8) -> &Node<T>;
    fn get_child_slot(&mut self, key: u8) -> &mut Node<T>;
    // return true if the container needs to grow to store a child for key
    fn should_grow(&self, key: u8) -> bool;
}

enum Node<T> {
    None,
    Leaf(T),
    Container(Box<dyn Container<T>>),
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
}

impl<T> Container<T> for Container4<T> {
    fn get_keys(&self) -> Vec<u8> {
        self.keys[0..self.count].to_vec()
    }
    fn should_grow(&self, key: u8) -> bool {
        if self.count < 4 {
            return false;
        }
        let c = self.get_child(key);
        matches!(c, Node::None)
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
        if self.count >= 4 {
            panic!("container should of been grown already");
        }
        let idx = self.count;
        self.keys[idx] = key;
        self.count += 1;
        &mut self.children[idx]
    }

    fn get_value(&self) -> Option<&T> {
        match &self.value {
            Node::Leaf(v) => Some(v),
            Node::None => None,
            _ => panic!("A Nodes value should always be a Leaf"),
        }
    }
    fn get_value_slot(&mut self) -> &mut Node<T> {
        &mut self.value
    }
    fn set_value(&mut self, v: Node<T>) {
        self.value = v;
    }
}

struct Container256<T> {
    children: [Node<T>; 256],
    value: Node<T>,
}

impl<T> Container256<T> {
    fn new(src: &mut Box<dyn Container<T>>) -> Container256<T> {
        let mut n = Container256 {
            children: arr![Node::None; 256],
            value: Node::None,
        };
        src.get_keys().into_iter().for_each(|k| {
            let x = src.get_child_slot(k);
            let y = n.get_child_slot(k);
            std::mem::swap(x, y);
        });
        std::mem::swap(src.get_value_slot(), n.get_value_slot());
        n
    }
}

impl<T> Container<T> for Container256<T> {
    fn get_value(&self) -> Option<&T> {
        match &self.value {
            Node::Leaf(v) => Some(v),
            Node::None => None,
            _ => panic!("A Nodes value should always be a Leaf"),
        }
    }
    fn should_grow(&self, _key: u8) -> bool {
        false
    }
    fn get_keys(&self) -> Vec<u8> {
        self.children
            .iter()
            .enumerate()
            .filter(|(_, n)| !matches!(n, Node::None))
            .map(|(i, _)| i as u8)
            .collect()
    }

    fn get_child(&self, key: u8) -> &Node<T> {
        &self.children[key as usize]
    }

    fn set_value(&mut self, v: Node<T>) {
        self.value = v;
    }
    fn get_value_slot(&mut self) -> &mut Node<T> {
        &mut self.value
    }
    fn get_child_slot(&mut self, key: u8) -> &mut Node<T> {
        &mut self.children[key as usize]
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
            if let Node::Container(c) = n {
                if c.should_grow(k[0]) {
                    *n = Node::Container(Box::new(Container256::new(c)));
                }
            }
            match n {
                Node::None => {
                    *n = Node::Container(Box::new(Container4::new()));
                }
                Node::Leaf(_) => {
                    let mut c = Box::new(Container4::new());
                    c.set_value(std::mem::take(n));
                    *n = Node::Container(c);
                }
                Node::Container(c) => {
                    n = c.get_child_slot(k[0]);
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
            Node::Container(c) => {
                c.set_value(Node::Leaf(value));
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
                Node::Container(c) => {
                    if k.is_empty() {
                        return c.get_value();
                    }
                    n = c.get_child(k[0]);
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
