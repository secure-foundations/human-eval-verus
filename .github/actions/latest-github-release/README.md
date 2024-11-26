Derived from https://github.com/marketplace/actions/get-latest-release


## Updating the code

### Setup

1. Install `vercel/ncc` by running this command in your terminal: `npm i -g @vercel/ncc`
2. Install modules.  I think this means running:
    ```
    npm install @actions/core
    npm install @actions/github
    npm install @octokit/rest
    ```

### Updates

After you change `main.js`, you need to run `ncc build main.js --license licenses.txt`,
which will update `dist/index.js`.


## References

- [GitHub REST APIs](https://docs.github.com/en/rest/releases/releases)
- [GitHub REST API Guide](https://docs.github.com/en/rest/guides/scripting-with-the-rest-api-and-javascript?apiVersion=2022-11-28)
- [Octokit docs](https://octokit.github.io/rest.js/v21/)
- [Creating a JavaScript action](https://docs.github.com/en/actions/sharing-automations/creating-actions/creating-a-javascript-action)
- [Another examples of getting releases](https://github.com/InsonusK/get-latest-release)
- [Writing GitHub workflows](https://docs.github.com/en/actions/writing-workflows/)
