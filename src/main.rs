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

trait Container<T: Sized> {
    fn get_value(&self) -> Option<&T>;
    fn get_child(&self, key: u8) -> &Node<T>;

    fn set_value(&mut self, v: Node<T>);
    fn get_child_slot(&mut self, key: u8) -> &mut Node<T>;
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
        let idx = self.count;
        self.keys[idx] = key;
        self.count += 1;
        return &mut self.children[idx];
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
                Node::Container(c) => {
                    n = c.get_child_slot(k[0]);
                    k = &k[1..];
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
