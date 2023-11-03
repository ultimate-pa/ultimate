#!/bin/bash

MAX_THREADS=25 TEMPLATE_FILE=add-sub.template   THREAD_PROCEDURE=Thread VERDICT=true ./generate-instances.sh
MAX_THREADS=25 TEMPLATE_FILE=incr-decr.template THREAD_PROCEDURE=Thread VERDICT=true ./generate-instances.sh

MAX_THREADS=11 OFFSET=1 MIN_ID=2 TEMPLATE_FILE=bluetooth-correct.template       THREAD_PROCEDURE=DeviceThread VERDICT=true  ./generate-instances.sh
MAX_THREADS=10 OFFSET=1 MIN_ID=2 TEMPLATE_FILE=bluetooth-customized.template    THREAD_PROCEDURE=DeviceThread VERDICT=true  ./generate-instances.sh
MAX_THREADS=10 OFFSET=1 MIN_ID=2 TEMPLATE_FILE=bluetooth-incorrect.template     THREAD_PROCEDURE=DeviceThread VERDICT=false ./generate-instances.sh
MAX_THREADS=10 OFFSET=0 MIN_ID=1 TEMPLATE_FILE=bluetooth-serverassert.template  THREAD_PROCEDURE=DeviceThread VERDICT=true  ./generate-instances.sh
