const core = require('@actions/core');
const { Octokit } = require("@octokit/rest");

const repository = core.getInput('repository');
const token = core.getInput('token');
var owner = core.getInput('owner');
var repo = core.getInput('repo');
var excludes = core.getInput('excludes').trim().split(",");
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
        console.log("releases");
        console.log(releases);
        var latest_release = releases[0];
        var release = latest_release;
        // // var release = await octokit.rest.repos.getLatestRelease({
        // //     owner: owner,
        // //     repo: repo,
        // //     });
        // //release = release.data;

        // var release = await octokit.rest.repos.getLatestRelease({
        //      owner: owner,
        //      repo: repo,
        //      });
        // release = release.data;
        var assets = await octokit.rest.repos.listReleaseAssets({
            owner: owner,
            repo: repo,
            release_id: release.id,
        });
        console.log("assets");
        console.log(assets);
        console.log(assets.length);

        for (const asset of assets.data) {
            console.log(asset);
            if (asset.name.indexOf(platform) >= 0) {
                core.setOutput('url', asset.url);
                break;
            }
        }
        // if (excludes.includes('prerelease')) {
        //     releases = releases.filter(x => x.prerelease != true);
        // }
        // if (excludes.includes('draft')) {
        //     releases = releases.filter(x => x.draft != true);
        // }
        // if (releases.length) {
        //     core.setOutput('release', releases[0].tag_name);
        //     core.setOutput('url', releases[0].url);
        //     //core.setOutput('id', String(releases[0].id));
        //     //core.setOutput('description', String(releases[0].body));
        // } else {
        //     core.setFailed("No valid releases");
        // }
    }
    catch (error) {
        core.setFailed(error.message);
    }
}

run()
