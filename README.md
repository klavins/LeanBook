# Lean Book

This book is compiled into HTML at [https://klavins.github.io/LeanBook](https://klavins.github.io/LeanBook). 

Chapters are in LeanBook/Chapters. To add a new chapter, make a file in that directory and then add an entry for the file to both LeanBook/Chapters/SUMMARY.lean and md/Makefile. 

To make the book, do
```
cd md
make
```

To serve the book do
```
mdbook serve --open
```

To "deploy" the book, do
```
make deploy
```
which copies the contents of md/book into the docs/ directory, which is where github-pages expects web pages to be. 