Here are some instructions to build a virtual box or a docker image with all the requirements installed to check the file.
The Virtual box installation is easier.
# Virtual Box 

Download a fresh debian image (e.g., https://www.linuxvmimages.com/images/debian-12/). Launch it using [Virtual Box](https://www.virtualbox.org/). 
In the running image, execute in a terminal:
```
sudo apt install -y curl
bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/amblafont/vscode-yade-example/master/images/install.sh)"
```

The installation script requires a debian running on amd64 architecture, but it could be adapted to an arm64 architecture.

# Docker

Install docker. Download the file [dockerfile](dockerfile) and save it in an empty directory. Go to this directory in a terminal, and execute the following sequence:
```
docker build -t yade .
```
And then,
```
# on windows, in a powershell terminal
docker run -ti --rm --privileged -e DISPLAY=:0 -v /run/desktop/mnt/host/wslg/.X11-unix:/tmp/.X11-unix yade
# on linux 
docker run -ti --rm --privileged -e DISPLAY=$DISPLAY -v /tmp/.X11-unix/:/tmp/.X11-unix/ yade
```
## Known issues
I couldn't find a simple way to make the dockerfile work on Apple silicon (modern Macs), even with rosetta enabled.
This is because the dockerfile extends [Coq's image](https://hub.docker.com/r/coqorg/coq) which assumes an amd64 architecture, while Apple silicon is arm64.
I believe that a [Coq's image for arm64](https://github.com/coq-community/docker-coq/issues/54) could be built without too much trouble.


