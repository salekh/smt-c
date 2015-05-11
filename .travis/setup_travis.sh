#!/usr/bin/env bash

git clone https://github.com/nafur/carl.git
cd carl/.travis/
source setup_travis.sh
source build.sh
cd ../../

if [[ ${TRAVIS_OS_NAME} == "linux" ]]; then

	source setup_ubuntu1204.sh

elif [[ ${TRAVIS_OS_NAME} == "osx" ]]; then

	source setup_osx.sh

fi

