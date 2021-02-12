use std::usize;

use arr_macro::arr;

fn main() {
    println!("Hello, world!");
    let mut x = Tree::<String>::new();
    x.put(&[1, 2], String::from("alice"));
    {
        x.put(&[1, 2, 3], String::from("bob"));
    }
    x.put(&[2, 10, 11], String::from("eve"));

    match x.get(&[1, 2, 3]) {
        Some(s) => println!("{}", s),
        None => println!("what the hell"),
    }
    match x.get(&[2, 10, 11]) {
        Some(s) => println!("{}", s),
        None => println!("what the hell 2"),
    }
    match x.get(&[1, 2]) {
        Some(s) => println!("{}", s),
        None => println!("what the hell 3"),
    }
    match x.get(&[1, 4]) {
        Some(_) => println!("what the hell 4"),
        None => println!("yay"),
    }
}

enum ChildSlot<'a, T: 'a> {
    Slot(&'a mut Node<T>),
    NoSpace,
}

trait Container<T: Sized> {
    fn get_value(&self) -> Option<&T>;
    fn get_value_node(&mut self) -> &mut Option<Node<T>>;
    fn get_child(&self, key: u8) -> &Node<T>;
    fn get_keys(&self) -> Vec<u8>;

    fn set_value(&mut self, v: Node<T>);
    fn get_child_slot(&mut self, key: u8) -> ChildSlot<T>;
}

enum Node<T: Sized> {
    None,
    Leaf(T),
    Container(Box<dyn Container<T>>),
}

impl<T: Sized> Default for Node<T> {
    fn default() -> Self {
        Node::None
    }
}

struct Container4<T: Sized> {
    children: [Node<T>; 4],
    value: Option<Node<T>>,
    count: usize,
    keys: [u8; 4],
}

impl<T: Sized> Container4<T> {
    fn new() -> Container4<T> {
        Container4::<T> {
            children: [Node::None, Node::None, Node::None, Node::None],
            value: None,
            count: 0,
            keys: [0; 4],
        }
    }
}

impl<T: Sized> Container<T> for Container4<T> {
    fn get_keys(&self) -> Vec<u8> {
        self.keys[0..self.count].to_vec()
    }
    fn get_value_node(&mut self) -> &mut Option<Node<T>> {
        return &mut self.value;
    }
    fn get_child(&self, key: u8) -> &Node<T> {
        for i in 0..self.count {
            if self.keys[i] == key {
                return &self.children[i];
            }
        }
        &Node::None
    }
    fn get_child_slot(&mut self, key: u8) -> ChildSlot<T> {
        for i in 0..self.count {
            if self.keys[i] == key {
                return ChildSlot::Slot(&mut self.children[i]);
            }
        }
        if self.count >= 4 {
            return ChildSlot::NoSpace;
        }
        let idx = self.count;
        self.keys[idx] = key;
        self.count += 1;
        return ChildSlot::Slot(&mut self.children[idx]);
    }

    fn get_value(&self) -> Option<&T> {
        match &self.value {
            Some(n) => match n {
                Node::Leaf(v) => Some(v),
                _ => panic!("A Nodes value should always be a Leaf"),
            },
            None => None,
        }
    }

    fn set_value(&mut self, v: Node<T>) {
        self.value = Some(v);
    }
}

struct Container256<T> {
    children: [Node<T>; 256],
    value: Option<Node<T>>,
}

impl<T: Sized> Container256<T> {
    fn new(srcn: &Node<T>) -> Container256<T> {
        let c = arr![Node::None; 256];
        let mut n = Container256 {
            children: c,
            value: None,
        };
        if let Node::Container(src) = srcn {
            src.get_keys().into_iter().for_each(|k| {
                let slot = src.get_child_slot(k);
                let dest = &mut n.children[k as usize];
                match slot {
                    ChildSlot::Slot(srcn) => {
                        std::mem::swap(dest, srcn);
                    }
                    ChildSlot::NoSpace => {
                        panic!("get_child_slot with a known existing key shouldn't return NoSpace")
                    }
                }
            });
            std::mem::swap(&mut n.value, src.get_value_node());
            return n;
        }
        panic!();
    }
}

impl<T: Sized> Container<T> for Container256<T> {
    fn get_value(&self) -> Option<&T> {
        match &self.value {
            Some(n) => match n {
                Node::Leaf(v) => Some(v),
                _ => panic!("A Nodes value should always be a Leaf"),
            },
            None => None,
        }
    }
    fn get_value_node(&mut self) -> &mut Option<Node<T>> {
        return &mut self.value;
    }
    fn get_keys(&self) -> Vec<u8> {
        self.children
            .iter()
            .enumerate()
            .filter(|(_, n)| if let Node::None = n { false } else { true })
            .map(|(i, _)| i as u8)
            .collect()
    }

    fn get_child(&self, key: u8) -> &Node<T> {
        &self.children[key as usize]
    }

    fn set_value(&mut self, v: Node<T>) {
        self.value = Some(v);
    }

    fn get_child_slot(&mut self, key: u8) -> ChildSlot<T> {
        ChildSlot::Slot(&mut self.children[key as usize])
    }
}

pub struct Tree<T: Sized> {
    root: Node<T>,
}

impl<T: Sized + 'static> Tree<T> {
    fn new() -> Self {
        Self { root: Node::None }
    }

    fn put(&mut self, key: &[u8], value: T) {
        let mut n = &mut self.root;
        let mut k = key;
        while k.len() > 0 {
            match n {
                Node::None => {
                    *n = Node::Container(Box::new(Container4::new()));
                }
                Node::Leaf(_) => {
                    let mut c = Box::new(Container4::<T>::new());
                    c.set_value(std::mem::take(n));
                    *n = Node::Container(c);
                }
                Node::Container(c) => match c.get_child_slot(k[0]) {
                    ChildSlot::Slot(s) => {
                        n = s;
                        k = &k[1..]
                    }
                    ChildSlot::NoSpace => {
                        let taken_n = std::mem::take(n);
                        if let Node::Container(nc) = taken_n {
                            *n = Node::Container(Box::new(Container256::new(&taken_n)))
                        }
                    }
                },
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

    fn get(&self, key: &[u8]) -> Option<&T> {
        let mut n = &self.root;
        let mut k = key;
        loop {
            match n {
                Node::Leaf(t) => {
                    if k.len() == 0 {
                        return Some(t);
                    } else {
                        return None;
                    }
                }
                Node::Container(c) => {
                    if k.len() == 0 {
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
