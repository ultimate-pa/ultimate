#!/bin/bash
# Small script that copies UAutomizer-Linux to the correct place for ir2boogie build on jenkins
rm -r /storage/jenkins/UAutomizer-linux/
cp -r UAutomizer-linux /storage/jenkins/
cp /storage/ultimate/trunk/examples/toolchains/AutomizerBpl.xml /storage/jenkins/UAutomizer-linux/config/
chown -R jenkins: /storage/jenkins/UAutomizer-linux
chmod a+w -R /storage/jenkins/UAutomizer-linux/configuration

