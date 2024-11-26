const core = require('@actions/core');
const { Octokit } = require("@octokit/rest");

const repository = core.getInput('repository');
const token = core.getInput('token');
var owner = core.getInput('owner');
var repo = core.getInput('repo');
//var excludes = core.getInput('excludes').trim().split(",");
var platform = core.getInput('platform');

const octokit = (() => {
  if (token) {
    return new Octokit({ auth: token,});
  } else {
    return new Octokit();
  }
})();

async function run() {
    try {
        if (repository){
                [owner, repo] = repository.split("/");
        }
        var releases  = await octokit.repos.listReleases({
            owner: owner,
            repo: repo,
            });
        releases = releases.data;
        //console.log("releases");
        //console.log(releases);
        var latest_release = releases[0];
        var release = latest_release;
        var assets = await octokit.rest.repos.listReleaseAssets({
            owner: owner,
            repo: repo,
            release_id: release.id,
        });
        //console.log("assets");
        //console.log(assets);

        for (const asset of assets.data) {
            console.log(asset.name);
            if (asset.name.indexOf(platform) >= 0) {
                core.setOutput('url', asset.browser_download_url);
                break;
            }
        }
        console.log("error: failed to find a matching asset");
    }
    catch (error) {
        core.setFailed(error.message);
    }
}

run()
