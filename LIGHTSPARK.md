# Sync the upstream repo

If you want to sync to the upstream, you'll need to _set_ the upstream. Do it like this:

```
git remote add upstream https://github.com/lightningdevkit/rust-lightning.git
```

You only need to do that once, after which `git remote -v` should output something like:

```
$ git remote -v
origin	git@github.com:lightsparkdev/rust-lightning-private.git (fetch)
origin	git@github.com:lightsparkdev/rust-lightning-private.git (push)
upstream	https://github.com/lightningdevkit/rust-lightning.git (fetch)
upstream	DISABLE (push)
```

Now, let's say that LDK releases a new tag and we want to sync to that. Here's the recipe! Below we assume that we're tracking `v0.0.116` on a branch called `lightspark/v0.0.116-branch`. The scenario is that LDK has released the "official" `v0.0.116` tag and we want to rebase our branch to that tag.

```
# Checkout main
git checkout main

# Fetch the upstream.
git fetch upstream

# Merge the upstream onto main
git merge upstream/main

# Pull to head
git pull

# Checkout your release branch.
git checkout lightspark/v0.0.116-branch

# Rebase the branch onto the new tag
git rebase --onto v0.0.116 origin/main

# Deal with merge conflicts... rinse and repeat:
git add foo
git rebase --continue

# Push the branch changes back.
git push -f
```
