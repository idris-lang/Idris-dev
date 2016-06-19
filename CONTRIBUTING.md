# Contributing to Idris-Dev

The Idris Community welcomes pull requests, bug reporting, and bug squashing!
However, we cannot do it all ourselves, and want to make it as easy as possible to contribute changes to get things working.
Here are a few guidelines that we would like contributors to follow so that we can have a chance of keeping on top of things.

## Getting Started

1. Make sure you are familiar with [Git](http://git-scm.com/book).
1. Make sure you have a [GitHub account](https://github.com/signup/free).
1. Make sure you are familiar with: [Idris](http://eb.host.cs.st-andrews.ac.uk/writings/idris-tutorial.pdf).
1. Make sure you can install Idris:
  * [Mac OS X](https://github.com/idris-lang/Idris-dev/wiki/Idris-on-OS-X-using-Homebrew)
  * [Ubuntu](https://github.com/idris-lang/Idris-dev/wiki/Idris-on-Ubuntu)
  * [Debian](https://github.com/idris-lang/Idris-dev/wiki/Idris-on-Debian)
  * [Windows](https://github.com/idris-lang/Idris-dev/wiki/Idris-on-Windows)

## Issue Reporting

Before you report an issue, or wish to add cool functionality please try and check to see if there are existing [issues](https://github.com/idris-lang/Idris-dev/issues) and [pull requests](https://github.com/idris-lang/Idris-dev/pulls).
We do not want you wasting your time, duplicating somebody's work!

## The Campsite Rule

We try to follow the **campsite rule**: leave the code base in better condition than you found it.
Please clean up any messes that you find, and don't leave behind new messes for the next contributor.

## Contributing to the default libraries.

Idris ships with a set of packages in `libs/` that is provided as a default library.

+ `prelude` is a collection of basic definitions, automatically imported by Idris programs.
+ `base` is tried and tested code that may be useful, and has seen active use in multiple projects.
+ `contrib` is code that is experimental in design and that we want to test before possible inclusion in `base`.
+ `effects` is a library which supports effectful programming.

These packages should not be seen as the *standard* as when working with dependent types; we do not necessarily know how best to work with dependent types yet.
These packages offer functionality that can be built on top of when constructing Idris programs.

Everything in prelude will be imported automatically, unless given the `--noprelude` option.
The contents of base are available with no special options, but modules must be imported.
The other two packages that ship with Idris, contrib and effects, require the use of the `-p` command-line argument to bring their contents into the include path.

New contributions should be added to the contrib package (never directly to base or prelude!).
If they turn out to be widely applicable and useful, they may later be moved into base.

As Idris is still being developed we are open to suggestions and changes that make improvements to these default packages.
Major changes to the library, or Idris itself, should be discussed first through the project's official channels of communication:

1. The mailing List.
1. On our IRC Channel `#idris` on freenode, or
1. As an RFC in the issue tracker

Developers then seeking to add content to Idris's prelude and default library, should do so through a PR where more discussions and refinements can be made.

We do not want you wasting your time nor duplicating somebody's work!

## Making Changes

Idris developers and hackers try to adhere to something similar to the [successful git branching model](http://nvie.com/posts/a-successful-git-branching-model/).
The steps are described below.

### New contributors

For those new to the project:

1. Fork our [main development repository](https://github.com/idris-lang/Idris-dev) `idris-dev` on github e.g.
2. Clone your fork to your local machine:

```
$ git clone git@github.com/<your github user name>/Idris-dev.git
```

3. Add `idris-lang/Idris-dev` as a remote upstream

```
$ git remote add upstream git@github.com:idris-lang/Idris-dev.git
```

### Existing Contributors

For those already contributing to the project:

1. Ensure your existing clone is up-to-date with current `HEAD` e.g.

```
$ git fetch upstream
$ git merge upstream/master
```

### Remaining Steps

The remaining steps are the same for both new and existing contributors:

1. Create, and checkout onto, a topic branch on which to base you work.
  * This is typically the master branch.
  * Please avoid working on the `master` branch.

```
$ git branch fix/master/my_contrib master
$ git checkout fix/master/my_contrib
```

1. Make commits of logical units.
1. Check for unnecessary whitespace with

```
$ git diff --check
```

1. Make sure your commit messages are along the lines of:

        Short (50 chars or less) summary of changes

        More detailed explanatory text, if necessary.  Wrap it to about 72
        characters or so.  In some contexts, the first line is treated as the
        subject of an email and the rest of the text as the body.  The blank
        line separating the summary from the body is critical (unless you omit
        the body entirely); tools like rebase can get confused if you run the
        two together.

        Further paragraphs come after blank lines.

        - Bullet points are okay, too

        - Typically a hyphen or asterisk is used for the bullet, preceded by a
          single space, with blank lines in between, but conventions vary here

1. Make sure you have added any necessary tests for your changes.
1. Run all the tests to ensure nothing else was accidentally broken.

```
$ make test
```

1. Push your changes to a topic branch in your fork of the repository.

```
$ git push origin fix/master/my_contrib
```

1. Go to GitHub and submit a pull request to `idris-dev`

From there you will have to wait on one of the `idris-dev` committers to respond to the request.
This response might be an accept or some changes/improvements/alternatives will be suggest.
We do not guarantee that all requests will be accepted.

## Increasing chances of acceptance.

To help increase the chance of your pull request being accepted:

1. Run the tests.
1. Update the documentation, the surrounding code, examples elsewhere, guides, whatever is affected by your contribution
1. Use appropriate code formatting for both Idris and Haskell.

## Additional Resources

* [Idris Wiki](https://github.com/idris-lang/Idris-dev/wiki);
* [Zen Of Idris](https://github.com/idris-lang/Idris-dev/wiki/The-Zen-of-Idris);
* Idris FAQs: [Official](https://idris.readthedocs.io/en/latest/faq/faq.html); [Unofficial](https://github.com/idris-lang/Idris-dev/wiki/Unofficial-FAQ);
* [Idris Manual](https://github.com/idris-lang/Idris-dev/wiki/Manual);
* [Idris Tutorial](https://idris.readthedocs.io/en/latest/tutorial/index.html);
* [Idris News](http://www.idris-lang.org/news/);
* [other Idris docs](http://www.idris-lang.org/documentation/).
* [Using Pull Requests](https://help.github.com/articles/using-pull-requests)
* [General GitHub Documentation](https://help.github.com/).


Adapted from the most excellent contributing files from the [Puppet project](https://github.com/puppetlabs/puppet) and [Factory Girl Rails](https://github.com/thoughtbot/factory_girl_rails/blob/master/CONTRIBUTING.md)
