def scmVars
def changeMessage
pipeline {
  agent { label 'linux' && 'java' }
  options {
    skipDefaultCheckout()
    timeout(time: 10, unit: 'HOURS')
    skipStagesAfterUnstable()
  }
  stages {
    stage('Checkout') {
      steps {
        script {
          scmVars = checkout scm
        }
      }
    }
    stage('Build and Test') {
      steps {
        sh('bash build.sh')
        withMaven {
          sh "cd trunk/source/BA_MavenParentUltimate && mvn -T 1C clean install"
        } 
      }
    }
    // stage('Report'){
    //   steps {
    //     junit keepLongStdio: true, testResults: 'prototype/test_results.xml'
    //     cobertura coberturaReportFile: 'prototype/cov-cobertura.xml'
    //     catchError(buildResult: 'SUCCESS', catchInterruptions: false) {
    //       //do not let coverage result errors fail the build 
    //       publishCoverage adapters: [coberturaAdapter('prototype/cov-cobertura.xml')], calculateDiffForChangeRequests: true, sourceFileResolver: sourceFiles('NEVER_STORE')
    //     }
    //   }
    // }
  }
  post {
    changed {
      script {
        env.mm_color = 'danger'
        if(currentBuild.currentResult == "SUCCESS") {
            env.mm_color = 'good'
        }
        def changeLogSets = currentBuild.changeSets
        changeMessage = ""
        for (int i = 0; i < changeLogSets.size(); i++) {
            def entries = changeLogSets[i].items
            for (int j = 0; j < entries.length; j++) {
                def entry = entries[j]
                changeMessage +="  * ${entry.commitId} by ${entry.author} on ${new Date(entry.timestamp)}: ${entry.msg}\n"
                // compute affected files and what was changed 
                // def files = new ArrayList(entry.affectedFiles)
                // for (int k = 0; k < files.size(); k++) {
                //     def file = files[k]
                //     echo "${file.editType.name} ${file.path}"
                // }
            }
        }
      }
      emailext(
        body: '$DEFAULT_CONTENT',
        mimeType: 'text/plain', 
        recipientProviders: [culprits(), developers(), requestor()], 
        replyTo: 'dietsch@informatik.uni-freiburg.de', 
        subject: '$DEFAULT_SUBJECT', 
        to: "${MAIL}"
      )
      mattermostSend( 
        color: "${env.mm_color}", 
        message: """Build ${currentBuild.id} of **${env.JOB_NAME}** finished with **${currentBuild.currentResult}**.
#### Links
* <${env.BUILD_URL}display/redirect|Open Jenkins log>
* <${env.RUN_CHANGES_DISPLAY_URL}|Open changes in Jenkins>
* <${scmVars.GIT_URL}|Open project in GitHub>
#### Changes
${changeMessage}
""",
        text: '', 
        channel: '#botpool', 
        icon: "https://jenkins.sopranium.de/static/0e41ff2a/images/jenkins-header-logo-v2.svg"
      )
    }
  }
}
