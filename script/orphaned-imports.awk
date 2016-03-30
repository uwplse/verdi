BEGIN {
    importing = 1

    import_regex = "Require|Import|Export"
}


# many Verdi files contain an Arguments command in the middle of the imports
# so we allow that here but do not count later occurences in the file
# as violations of the "imports first" rule
! ($0 ~ import_regex || /Arguments/ || /^[[:space:]]*$/) {
  importing = 0 \
}

$0 ~ import_regex {
    if (importing == 0) {
        printf("Orphaned import in %s!\n", FILENAME)
        printf("%s\n", $0)
    }
}
