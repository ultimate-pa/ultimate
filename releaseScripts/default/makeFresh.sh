#!/bin/bash
# This script builds Ultimate with Maven and then creates deployable zip archives for 
# all tools.
# Note that it does no longer build the website, as this requires Ruby and Jekyll.
# If you want to build the website, use makeWebsite.sh after makeFresh.sh.


# load shared functions and settings
DIR="${BASH_SOURCE%/*}"
if [[ ! -d "$DIR" ]]; then DIR="$PWD"; fi
. "$DIR/makeSettings.sh"

verlte() {
  printf '%s\n%s' "$1" "$2" | sort -C -V
}

build() {
  spushd "../../trunk/source/BA_MavenParentUltimate/"
  if ! command -v mvn  &> /dev/null ; then
    echo "Maven not found. Please install Maven and make sure it is in your PATH."
    exit 1
  fi
  mvn_version=$(mvn --version)
  java_version=$(grep -oP 'Java version: \K.*?,' <<< "$mvn_version")
  java_version=${java_version::-1} # remove ,
  if verlte "$java_version" "21.0.0"; then
    echo "Java version $java_version is too old. Please install Java 21 or newer."
    exit 1
  fi
  printf 'Using the following versions:\n%s\n' "$mvn_version"
  exit_on_fail mvn -T 1C clean install -Pmaterialize
  spopd
}

create_tool_zips() {
  for platform in {linux,win32}; do
    # makeZip <toolname> <targetarch> <reachtc> <termtc> <witnessvaltc> <memsafetytc> <ltlc> <termwitnessvaltc>
    # Taipan
    exit_on_fail bash makeZip.sh Taipan $platform AutomizerCInline_IcfgBuilder_WitnessPrinter.xml NONE AutomizerCInline_IcfgBuilder.xml AutomizerCInline_IcfgBuilder_WitnessPrinter.xml NONE NONE

    # Automizer without separate blockencoding plugin
    exit_on_fail bash makeZip.sh Automizer $platform AutomizerCInline_IcfgBuilder_WitnessPrinter.xml BuchiAutomizerCInline_IcfgBuilder_WitnessPrinter.xml AutomizerCInline_IcfgBuilder.xml AutomizerCInline_IcfgBuilder_WitnessPrinter.xml LTLAutomizerC.xml BuchiAutomizerCInline_IcfgBuilder.xml

    # Automizer with separate blockencoding plugin
    #exit_on_fail bash makeZip.sh Automizer linux AutomizerC_BE_WitnessPrinter.xml BuchiAutomizerCInline_BE_WitnessPrinter.xml AutomizerC.xml AutomizerC_BE_WitnessPrinter.xml LTLAutomizerC.xml BuchiAutomizerCInline.xml

    # Kojak
    exit_on_fail bash makeZip.sh Kojak $platform KojakC_IcfgBuilder_WitnessPrinter.xml NONE KojakC_IcfgBuilder.xml KojakC_IcfgBuilder_WitnessPrinter.xml NONE NONE

    # GemCutter
    exit_on_fail bash makeZip.sh GemCutter $platform AutomizerCInline_IcfgBuilder_WitnessPrinter.xml NONE AutomizerCInline_IcfgBuilder.xml AutomizerCInline_IcfgBuilder_WitnessPrinter.xml NONE NONE

    # Referee
    exit_on_fail bash makeZip.sh Referee $platform RefereeCInline_IcfgBuilder.xml NONE RefereeCInline_IcfgBuilder.xml NONE NONE NONE

    # DeltaDebugger
    exit_on_fail bash createDeltaDebuggerDir.sh $platform

    # ReqCheck
    exit_on_fail bash createReqCheckZip.sh ReqCheck $platform ReqCheck.xml ReqCheck.xml
  done
}

create_webbackend_dir() {
  local source="../../trunk/source/BA_SiteRepository/target/products/WebBackend/linux/gtk/x86_64"
  local target="$(readlink -f WebBackend)"
  if [ -d "$target" ] ; then rm -r "$target" ; fi
  mkdir "$target"
  echo "Copying WebBackend"
  cp -r "$source/"* "$target"
}

build
create_tool_zips
create_webbackend_dir
