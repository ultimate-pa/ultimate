def scmVars
@Library('jenkins-shared-lib') _

pipeline {
  agent { label 'linux && java' }
  options {
    skipDefaultCheckout()
    timeout(time: 12, unit: 'HOURS')
    timestamps()
  }
  environment {
    PATH = "${env.WORKSPACE}/releaseScripts/default/adds:${env.PATH}"
  }
  stages {
    stage('Checkout') {
      steps {
        script {
          scmVars = checkout scm
        }
        sh 'git clean -f -x -d'
      }
    }
    stage('Check environment') {
      steps {
        sh(label: 'check solvers', script: 'releaseScripts/default/check_solvers.sh')
      }
    }
    stage('Build and run basic tests') {
      steps {
        withMaven(options: [artifactsPublisher(disabled: true)]) {
          sh 'cd trunk/source/BA_MavenParentUltimate && mvn -T 1C clean install'
        }
      }
    }
  }
  post {
    unsuccessful {
      script { string mmMessage = mattermost.create_mattermost_message(scmVars) }
      emailext(body: '$DEFAULT_CONTENT', mimeType: 'text/plain', recipientProviders: [culprits(), developers(), requestor()], replyTo: 'dietsch@informatik.uni-freiburg.de', subject: '$DEFAULT_SUBJECT')
      mattermostSend(color: "${env.mm_color}", message: "${mmMessage}", text: '', channel: '#ultimate', icon: "https://jenkins.sopranium.de/static/0e41ff2a/images/jenkins-header-logo-v2.svg")
    }
    fixed {
      script { string mmMessage = mattermost.create_mattermost_message(scmVars) }
      emailext(body: '$DEFAULT_CONTENT', mimeType: 'text/plain', recipientProviders: [culprits(), developers(), requestor()], replyTo: 'dietsch@informatik.uni-freiburg.de', subject: '$DEFAULT_SUBJECT')
      mattermostSend(color: "${env.mm_color}", message: "${mmMessage}", text: '', channel: '#ultimate', icon: "https://jenkins.sopranium.de/static/0e41ff2a/images/jenkins-header-logo-v2.svg")
    }
  }
}
