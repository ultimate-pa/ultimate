# Package Ultimate for Docker

## Build Ultimate Docker images
An Ultimate `PRODUCT` can be built with the following Docker call

```shell
docker build -t <PRODUCT> --target <PRODUCT> .
```

where `PRODUCT` is a placeholder for one of the products

  - `ultimate-cli`
  - `ultimate-debug`
  - `ultimate-reqanalyzer`
  - `ultimate-deltadebugger`
  - `ultimate-eliminator`
  - `ultimate-webbackend`

shipped with the Ultimate program analysis framework.

For validating the built Ultimate `PRODUCT` image, you can create and run a Docker container based on this image with the following Docker call.
```shell
docker run -it <PRODUCT>
```
As an expected result, you should then receive the Ultimate version output from the executed Ultimate `PRODUCT` in the container.


## Run Ultimate Docker containers

If you want to run Ultimate interactively for any verification input, you can spwan a bash in a created and started Ultimate `PRODUCT` container as follows.
```shell
docker run -it <PRODUCT> /bin/bash
Ultimate -tc <TOOLCHAIN> -s <SETTINGS> -i <PROGRAM>
```
Calling Ultimate within the container then follows as usual, where a `TOOLCHAIN`, `SETTINGS`, and `PROGRAM` file path should be specified for a verification run.


## Configure Ultimate Webbackend

The specific Ultimate `PRODUCT` called `ultimate-webbackend` requires an extensive and valid configuration for the Web service to start.


