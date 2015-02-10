#!/usr/bin/env bash

DASH="uwplse@uwplse.org:/var/www/verdi"

rsync --quiet --recursive . "$DASH"
