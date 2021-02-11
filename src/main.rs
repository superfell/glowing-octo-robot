fn main() {
    println!("Hello, world!");
    let mut x = Tree::<&str>::new();
    x.put(&[1, 2, 3], "bob");
    println!("{}", x.get(&[1, 2, 3]).unwrap());
}

trait Container<T: Sized> {
    fn set_child(&mut self, key: u8, child: Node<T>);
    fn get_child(&self, key: u8) -> &Node<T>;
    fn get_value(&self) -> Option<&T>;
}

enum Node<T> {
    None,
    Leaf(T),
    Container(Box<dyn Container<T>>),
}

struct Node4<T: Sized> {
    values: [Node<T>; 4],
    count: usize,
    keys: [u8; 4],
}

impl<T> Container<T> for Node4<T> {
    fn set_child(&mut self, key: u8, child: Node<T>) {
        self.keys[self.count] = key;
        self.values[self.count] = child;
        self.count += 1;
    }

    fn get_child(&self, key: u8) -> &Node<T> {
        for i in 0..self.count {
            if self.keys[i] == key {
                return &self.values[i];
            }
        }
        &Node::None
    }
    fn get_value(&self) -> Option<&T> {
        todo!()
    }
}

pub struct Tree<T> {
    root: Node<T>,
}

impl<T: 'static> Tree<T> {
    fn new() -> Self {
        let n4 = Box::new(Node4::<T> {
            keys: [0, 0, 0, 0],
            values: [Node::None, Node::None, Node::None, Node::None],
            count: 0,
        });
        Self {
            root: Node::Container(n4),
        }
    }
    fn put(&mut self, key: &[u8], value: T) {
        match &mut self.root {
            Node::None => panic!(),
            Node::Container(c) => {
                c.set_child(key[0], Node::Leaf(value));
            }
            Node::Leaf(t) => panic!(),
        }
    }

    fn get(&self, key: &[u8]) -> Option<&T> {
        let mut n = &self.root;
        let mut k = key;
        loop {
            n = match n {
                Node::Leaf(t) => {
                    if k.len() == 0 {
                        return Some(&t);
                    } else {
                        return None;
                    }
                }
                Node::Container(c) => {
                    if k.len() == 0 {
                        return c.get_value();
                    }
                    n = c.get_child(key[0]);
                    k = &k[1..];
                    n
                }
                Node::None => return None,
            };
        }
    }
}
