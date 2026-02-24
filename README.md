
How to build minibash
---------------------

1. Build libtommy
```
(cd tommyds; make)
```

2. Build libtree-sitter.a
```
(cd tree-sitter; make)
```

3. Build minibash

```
cd src
make
```

4. To use the tree-sitter CLI tool, it is recommended to
```
source env.sh
```

5. Test the tree-sitter tool with with
```
tree-sitter parse tests/001-comment.sh
```
(The `tree-sitter` example must be separately installed; ours is in
`~cs3214/bin`)

6. Build the tests

```
(cd tests; make)
```

7. On rlogin, you may run the tests by invoking 

```
minibash_driver.py
```

On rlogin, this will pick up `minibash_driver.py` installed in our class directory.

Use `../tests/minibash_driver.py` if you wish to run your copy of tests.

