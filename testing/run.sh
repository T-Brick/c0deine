#!/bin/bash
NODE=${NODE:=$(which node)}

exec $NODE run.js $@
