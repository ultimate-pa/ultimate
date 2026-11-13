#!/bin/bash
# Small script that copies UAutomizer-Linux to the correct place for ir2boogie build on jenkins
rm -r /storage/jenkins/UAutomizer-linux-x86_64/
cp -r UAutomizer-linux-x86_64 /storage/jenkins/
cp /storage/ultimate/trunk/examples/toolchains/AutomizerBpl.xml /storage/jenkins/UAutomizer-linux-x86_64/config/
chown -R jenkins: /storage/jenkins/UAutomizer-linux-x86_64
chmod a+w -R /storage/jenkins/UAutomizer-linux-x86_64/configuration

