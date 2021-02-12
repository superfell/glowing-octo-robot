fn main() {
    println!("Hello, world!");
    let mut x = Tree::<Box<&str>>::new();
    {
        x.put(&[1, 2, 3], Box::new("bob"));
        println!("{}", x.get(&[1, 2, 3]).unwrap());
    }
}

trait Container<T: Sized + Clone> {
    fn get_value(&self) -> Option<&T>;
    fn get_child(&self, key: u8) -> &Node<T>;

    fn set_value(&mut self, value: T);
    fn set_child(&mut self, key: u8, child: Node<T>);
    fn get_child_slot(&mut self, key: u8) -> (&Node<T>, usize);
    fn set_child_slot(&mut self, child: Node<T>, slot: usize);
}

enum Node<T: Sized + Clone> {
    None,
    Leaf(T),
    Container(Box<dyn Container<T>>),
}

struct Node4<T: Sized + Clone> {
    values: [Node<T>; 4],
    count: usize,
    keys: [u8; 4],
}

impl<T: Sized + Clone> Node4<T> {
    fn new() -> Node4<T> {
        Node4::<T> {
            values: [Node::None, Node::None, Node::None, Node::None],
            count: 0,
            keys: [0, 0, 0, 0],
        }
    }
}

impl<T: Sized + Clone> Container<T> for Node4<T> {
    fn get_child(&self, key: u8) -> &Node<T> {
        for i in 0..self.count {
            if self.keys[i] == key {
                return &self.values[i];
            }
        }
        &Node::None
    }
    fn get_child_slot(&mut self, key: u8) -> (&Node<T>, usize) {
        for i in 0..self.count {
            if self.keys[i] == key {
                return (&self.values[i], i);
            }
        }
        let idx = self.count;
        self.keys[idx] = key;
        let next = &self.values[idx];
        self.count += 1;
        return (next, idx);
    }

    fn set_child_slot(&mut self, child: Node<T>, slot: usize) {
        self.values[slot] = child;
    }

    fn set_child(&mut self, key: u8, child: Node<T>) {
        self.keys[self.count] = key;
        self.values[self.count] = child;
        self.count += 1;
    }

    fn get_value(&self) -> Option<&T> {
        todo!()
    }
    fn set_value(&mut self, _child: T) {}
}

pub struct Tree<T: Sized + Clone> {
    root: Node<T>,
}

impl<T: Sized + Clone + 'static> Tree<T> {
    fn new() -> Self {
        Self { root: Node::None }
    }

    fn put(&mut self, key: &[u8], value: T) {
        let mut r = Node::<T>::None;
        std::mem::swap(&mut r, &mut self.root);
        self.root = put_next(&mut r, key, value);
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
                    let nc = c.get_child(key[0]);
                    k = &k[1..];
                    &nc
                }
                Node::None => return None,
            };
        }
    }
}

fn put_next<T: Sized + Clone + 'static>(n: &mut Node<T>, key: &[u8], value: T) -> Node<T> {
    if key.len() == 0 {
        return match n {
            Node::None => Node::Leaf(value),
            Node::Container(c) => {
                c.set_value(value);
                n
            }
            Node::Leaf(_) => Node::Leaf(value),
        };
    }
    let mut nc: Box<dyn Container<T>> = match n {
        Node::None => Box::new(Node4::new()),
        Node::Container(mut c) => c,
        Node::Leaf(v) => {
            let mut b: Box<dyn Container<T>> = Box::new(Node4::new());
            b.set_value(v.clone());
            b
        }
    };
    let (child, slot) = nc.get_child_slot(key[0]);
    let newChild = put_next(&mut child, &key[1..], value);
    nc.set_child_slot(newChild, slot);
    return Node::Container(nc);
}
