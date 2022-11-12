def scmVars
mmMessage = ''

def prepare_post(def scmResult) {
  switch(currentBuild.currentResult) {
    case 'SUCCESS':
      env.mm_color = 'good'
      break
    case 'UNSTABLE':
      env.mm_color = '#ebc934'
      break
    default:
      env.mm_color = 'danger'
      break
  }

  def changeLogSets = currentBuild.changeSets
  def changeMessage = ""
  for (int i = 0; i < changeLogSets.size(); i++) {
      def entries = changeLogSets[i].items
      for (int j = 0; j < entries.length; j++) {
          def entry = entries[j]
          changeMessage +="  * ${entry.commitId} by ${entry.author} on ${new Date(entry.timestamp)}: ${entry.msg}\n"
      }
  }
  mmMessage = """Build ${currentBuild.id} of **${java.net.URLDecoder.decode env.JOB_NAME, 'UTF-8'}** finished with **${currentBuild.currentResult}**.
#### Links
* <${env.BUILD_URL}display/redirect|Open Jenkins log>
* <${env.RUN_CHANGES_DISPLAY_URL}|Open changes in Jenkins>
"""
  if(scmResult){
    mmMessage += """
* <${scmResult.GIT_URL}|Open project in GitHub>
"""
  }
  mmMessage += """
#### Changes
${changeMessage}
"""
}


pipeline {
  agent { label 'linux && java' }
  options {
    skipDefaultCheckout()
    timeout(time: 12, unit: 'HOURS')
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
      script { prepare_post(scmVars) }
      emailext(body: '$DEFAULT_CONTENT', mimeType: 'text/plain', recipientProviders: [culprits(), developers(), requestor()], replyTo: 'dietsch@informatik.uni-freiburg.de', subject: '$DEFAULT_SUBJECT')
      mattermostSend(color: "${env.mm_color}", message: "${mmMessage}", text: '', channel: '#ultimate', icon: "https://jenkins.sopranium.de/static/0e41ff2a/images/jenkins-header-logo-v2.svg")
    }
    fixed {
      script { prepare_post(scmVars) }
      emailext(body: '$DEFAULT_CONTENT', mimeType: 'text/plain', recipientProviders: [culprits(), developers(), requestor()], replyTo: 'dietsch@informatik.uni-freiburg.de', subject: '$DEFAULT_SUBJECT')
      mattermostSend(color: "${env.mm_color}", message: "${mmMessage}", text: '', channel: '#ultimate', icon: "https://jenkins.sopranium.de/static/0e41ff2a/images/jenkins-header-logo-v2.svg")
    }
  }
}
