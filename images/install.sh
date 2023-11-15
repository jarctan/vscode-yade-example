echo "This script ought to be executed on a fresh debian system."
echo "It installs all the requirements to try the vscode extension coreact-yade on https://github.com/amblafont/vscode-yade-example"
echo "*************"
echo "Installing curl"
echo "*************"
sudo apt install -y curl

echo "*************"
echo "Installing vscode"
echo "*************"
curl -L "https://code.visualstudio.com/sha/download?build=stable&os=linux-deb-x64" --output code.deb
sudo apt install -y ./code.deb

echo "*************"
echo "Installing opam"
echo "*************"
sudo apt install -y opam 
opam init -y
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam update

echo "*************"
echo "Installing coq, coq-lsp, and hierarchy builder"
echo "*************"
opam install --confirm-level=unsafe-yes coq coq-lsp coq-hierarchy-builder

echo "*************"
echo "Installing coreact-yade"
echo "*************"
curl  -L https://github.com/amblafont/graph-editor-web/releases/download/v0.3-alpha/coreact-yade_1.1.0_amd64.deb --output yade.deb
sudo apt install -y ./yade.deb
code --install-extension amblafont.coreact-yade

echo "*************"
echo "Preparing the example directory"
echo "*************"
git clone https://github.com/amblafont/vscode-yade-example.git
cd vscode-yade-example && make

echo "*************"
echo "Finished!"
echo "*************"
echo "Now, run 'eval \$(opam env) ; code vscode-yade-example -a example.v'"


