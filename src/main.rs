fn main() {
    println!("Hello, world!");
    let mut x = Tree::<Box<&str>>::new();
    {
        x.put(&[1, 2, 3], Box::new("bob"));
        x.put(&[2, 10, 11], Box::new("eve"));
        match x.get(&[1, 2, 3]) {
            Some(s) => println!("{}", s),
            None => println!("what the hell"),
        }
        match x.get(&[2, 10, 11]) {
            Some(s) => println!("{}", s),
            None => println!("what the hell 2"),
        }
    }
}

trait Container<T: Sized + Clone> {
    fn get_value(&self) -> Option<&T>;
    fn get_child(&self, key: u8) -> &Node<T>;

    fn set_value(&mut self, v: T);
    fn get_child_slot(&mut self, key: u8) -> &mut Node<T>;
}

enum Node<T: Sized + Clone> {
    None,
    Leaf(T),
    Container(Box<dyn Container<T>>),
}

struct Container4<T: Sized + Clone> {
    values: [Node<T>; 4],
    count: usize,
    keys: [u8; 4],
}

impl<T: Sized + Clone> Container4<T> {
    fn new() -> Container4<T> {
        Container4::<T> {
            values: [Node::None, Node::None, Node::None, Node::None],
            count: 0,
            keys: [0, 0, 0, 0],
        }
    }
}

impl<T: Sized + Clone> Container<T> for Container4<T> {
    fn get_child(&self, key: u8) -> &Node<T> {
        for i in 0..self.count {
            if self.keys[i] == key {
                return &self.values[i];
            }
        }
        &Node::None
    }
    fn get_child_slot(&mut self, key: u8) -> &mut Node<T> {
        for i in 0..self.count {
            if self.keys[i] == key {
                return &mut self.values[i];
            }
        }
        let idx = self.count;
        self.keys[idx] = key;
        self.count += 1;
        return &mut self.values[idx];
    }

    fn get_value(&self) -> Option<&T> {
        todo!()
    }
    fn set_value(&mut self, _child: T) {
        todo!()
    }
}

pub struct Tree<T: Sized + Clone> {
    root: Node<T>,
}

impl<T: Sized + Clone + 'static> Tree<T> {
    fn new() -> Self {
        Self { root: Node::None }
    }

    fn put(&mut self, key: &[u8], value: T) {
        let mut n = &mut self.root;
        let mut k = key;
        loop {
            if k.len() == 0 {
                match n {
                    Node::None => {
                        *n = Node::Leaf(value);
                    }
                    Node::Leaf(v) => {
                        *v = value;
                    }
                    Node::Container(c) => {
                        c.set_value(value);
                    }
                }
                return;
            }
            match n {
                Node::None => {
                    *n = Node::Container(Box::new(Container4::new()));
                }
                Node::Leaf(_) => {
                    let c = Box::new(Container4::<T>::new());
                    // TODO how do we move this leaf into the new container?
                    // c.set_value(n);
                    *n = Node::Container(c);
                }
                Node::Container(c) => {
                    n = c.get_child_slot(k[0]);
                    k = &k[1..];
                }
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
