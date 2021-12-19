# Representation Theory of Finite Groups

In this project, the Lean language is used to study the representation theory of finite groups.

## Build

Use the following command to build the project.

```bash
$ leanproject --build
```

## Code Structure

Please refer to the comments in individual files for the details.

Start with the `default.lean` file under each directory.

### Basic

In `./src/basic/`, basic concepts like `finite_group` and `representation` are defined.

$Z_3$ group is used as an example.

### 3-Dimensional Linear Space

In `./src/linear_space3/`, the 3-dimensional linear space on real numbers ($\R$) is defined.

### General Linear Space

See `./src/linear_space/` where more general linear spaces with any finite dimension are defined.

### Matrix Representation

In `./src/matrix_representation.lean`, the general linear group (`invertible_matrix`) is shown as a general representation of groups.

### Schur's Lemma

The two parts of Schur's Lemma are defined in `./src/schur_lemma.lean`. 

### Examples

See `./src/examples/` for another three examples.

## Known Issues

There are several `sorry`s in the code. Most of them are too complicated to be solved, due to the lack of time.
