import json
from requests import Request
import re

JENKINS_PROJECT = "Ultimate/Ultimate Nightly"
FLAKY_THRESHOLD = 3


def get_latest_builds_with_tests(server, job_name, n=1):
    res = []
    for b in server.get_job_info(f"{JENKINS_PROJECT}/{job_name}")["builds"]:
        build_info = get_build_info(server, job_name, b["number"])
        # Check if there is a test-report for the given build
        actions = build_info["actions"]
        if any(a.get("urlName", "") == "testReport" for a in actions):
            res.append(build_info)
            if len(res) == n:
                break
    return res


def get_build_info(server, job_name, build_number):
    return server.get_build_info(f"{JENKINS_PROJECT}/{job_name}", build_number)


def get_test_results(server, build_info):
    # Use Request to provide tree-params for a way smaller test-results
    req = Request("GET", build_info["url"] + "testReport/api/json",
                  params="tree=suites[cases[name,className,duration,status]]")
    res = {}
    for suite in json.loads(server.jenkins_open(req))["suites"]:
        for case in suite["cases"]:
            correct = case["status"] in ["PASSED", "FIXED"]
            res[case['className'], case['name']] = correct, case["duration"]
    return res


# TODO: Should we also compare the times?
def compare_test_results(server, build_info, reference_build_info):
    results = get_test_results(server, build_info)
    reference_results = get_test_results(server, reference_build_info)
    new_failures = []
    for name, (res, time) in results.items():
        if name not in reference_results:
            continue
        ref_res, ref_time = reference_results[name]
        if ref_res and not res:
            new_failures.append(name)
    return new_failures


def find_flaky_tests(server, job_name, number_of_builds):
    builds = get_latest_builds_with_tests(server, job_name, number_of_builds)
    test_results = [(get_test_results(server, b), b["number"])
                    for b in reversed(builds)]
    all_tests = set()
    for t, _ in test_results:
        all_tests.update(t.keys())
    res = {}
    for name in all_tests:
        last_result = True
        new_failures = []
        for t, build in test_results:
            if name not in t:
                continue
            result = t[name][0]
            if last_result != result:
                last_result = result
                if not result:
                    new_failures.append(build)
        if len(new_failures) >= FLAKY_THRESHOLD:
            res[name] = new_failures
    return res


# TODO: This is quite hacky (but seems to work), is there a better way?
def get_test_url(base_url, test_class, test_name):
    formatted_class = '/'.join(test_class.rsplit('.', 1))
    formatted_name = re.sub(r'[^\w\d]', "_", test_name)
    return f"{base_url}testReport/{formatted_class}/{formatted_name}"


def format_build(build_info):
    return f'[{build_info["displayName"]}]({build_info["url"]})'


def format_comparison(server, build_info, reference_build_info):
    failures = compare_test_results(server, build_info, reference_build_info)
    compared = f'Compared the latest nightly build {format_build(build_info)}'\
               f' with the build {format_build(reference_build_info)} of the '\
               'reference branch.'
    if not failures:
        return f"{compared}\n\nNo additional tests failed there."
    url = build_info['url']
    formatted = "\n".join(f"* [{n} ({c})]({get_test_url(url, c, n)})"
                          for c, n in sorted(failures))
    return f'{compared}\n\nThe following {len(failures)} tests failed:\n'\
           f'{formatted}\n\n'\
           'Please check these tests before merging this PR.'


def compare_jobs_on_latest_build(server, job_name, reference_job_name):
    build = get_latest_builds_with_tests(server, job_name)[0]
    ref_build = get_latest_builds_with_tests(server, reference_job_name)[0]
    return format_comparison(server, build, ref_build)


def get_commit_ids(build_info):
    res = set()
    for c in build_info["changeSets"]:
        for i in c["items"]:
            res.add(i["commitId"])
    return res


def check_pull_requests(server, gh_repo, reference_job_name):
    ref_build = get_latest_builds_with_tests(server, reference_job_name)[0]
    for j in server.get_job_info(JENKINS_PROJECT)["jobs"]:
        # Since we have unstable tests, "yellow" means that those were executed
        if j["color"] != "yellow":
            continue
        m = re.match(r"PR-(\d+)", j["name"])
        if not m:
            continue
        build = get_latest_builds_with_tests(server, j["name"])[0]
        # Continue if there are no more changes in build compared to ref_build
        # TODO: Is there a better way to check for an "initial" build?
        if build["number"] > 1 and \
           get_commit_ids(build) <= get_commit_ids(ref_build):
            continue
        pr = gh_repo.get_pull(int(m.group(1)))
        pr.create_issue_comment(format_comparison(server, build, ref_build))


# TODO: To run the script you need to add:
# - from jenkins import Jenkins
# - server = Jenkins(JENKINS_URL, JENKINS_USER, JENKINS_TOKEN)
#   to pass to compare_jobs_on_latest_build (you need a jenkins-token)
