# Docker Packaging and Deployment of Ultimate Products

## Build Ultimate Docker images

An Ultimate `PRODUCT` can be built with the following Docker call

```shell
docker build --platform linux/amd64 --tag <PRODUCT> --target <PRODUCT> .
```

where `PRODUCT` is a placeholder for one of the pre-configured products

  - `ultimate-automizer`
  - `ultimate-deltadebugger`
  - `ultimate-eliminator`
  - `ultimate-gemcutter`
  - `ultimate-kojak`
  - `ultimate-referee`
  - `ultimate-reqanalyzer`
  - `ultimate-taipan`
  - `ultimate-webbackend`
  - `ultimate-webfrontend`

or one of the basic products without any configuration (e.g., for your own Docker images or for debugging and development)

  - `ultimate-cli`
  - `ultimate-debug`

shipped with the Ultimate program analysis framework.

> [!NOTE]
> Building the Ultimate product images is currently limited to the Docker target platform `linux/amd64` (Linux containers for the 64-bit x86 architecture).
> However, these images can still be used on a Windows system with [Docker Desktop](https://docs.docker.com/desktop/setup/install/windows-install/) configured with the WSL2 or Hyper-V backend in order to create and run Linux containers on a Windows system.

For validating the built Ultimate `PRODUCT` image, you can create and run a Docker container based on this image with the following Docker call.
```shell
docker run -it <PRODUCT>
```
As an expected result, you should then receive the Ultimate version output from the executed Ultimate `PRODUCT` in the container.


## Run Ultimate Docker containers

If you want to run Ultimate interactively for any verification input, you can spwan a bash in a created and started Ultimate `PRODUCT` container as follows.
```shell
docker run -it <PRODUCT>
<PRODUCT> -tc <TOOLCHAIN> -s <SETTINGS> -i <PROGRAM>
```
Calling the Ultimate `PRODUCT` within the container then follows as usual, where a `TOOLCHAIN`, `SETTINGS`, and `PROGRAM` file should be specified for a verification run.

> [!NOTE]
> The pre-configured products are already provided with the appropriate configuration (toolchain and setting files).
> You can access the configuration directory within a Docker container via the environment variable `ULTIMATE_CONFIG_PATH`.

An exception is a start of the graphical Ultimate Debug UI.
To do this, a graphic connection to the host system must be established via the X11 protocol, which can be done with the following Docker call.
```shell
docker run -it --network host \
           -e DISPLAY=$DISPLAY \
           -v <XAUTHORITY>:/home/ultimate/.Xauthority \
           -v /tmp/.X11-unix:/tmp/.X11-unix \
           ultimate-debug
```
Note that the Docker call requires an `XAUTHORITY` file from the host system to grant the Ultimate Debug UI in the Docker container access to the graphical session on the host.
An `XAUTHORITY` file is, in the case of an X11 session, often located in the user's home directory on the host system and usually named `.Xauthority`.
In the case of a Wayland session, the `XAUTHORITY` file is often located under `/run/user/*/.*Xwaylandauth*`.
The `XAUTHORITY` file is mounted into the container by Docker along with a temporary Unix X11 socket to establish an X11 connection between host and container.
The Ultimate Debug UI application then uses this connection to render its graphical interface outside of the container on the host system.


## Run Ultimate WebBackend and Frontend

The specific Ultimate `PRODUCT`s called `ultimate-webbackend` and `ultimate-webfrontend` require an extensive and valid configuration for the Web service to start.
An example configuration is provided by a Docker Compose setup that can be configured by environemnt variables in the `ultimate-webservice.env` file.
After optional adjustment of the configuration, the setup can be provisioned using Docker Compose:
```shell
docker compose --env-file ultimate-webservice.env up --build
```
The frontend of the Web service can be reached via the following URL in the web browser when using the example configuration: [http://localhost:80/website/](http://localhost:80/website/).
