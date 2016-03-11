#!/usr/bin/env awk -f

BEGIN {
  printf("<table>\n")
  FS = ","
}

{
  printf("<tr>\n")
  for(i=1; i<=NF; i++) {
    if(NR==1) {
      printf("\t<th>\n\t\t%s\n\t</th>\n", $i)
    } else {
      printf("\t<td>\n\t\t%s\n\t</td>\n", $i)
    }
  }
  printf("</tr>\n")
}

END {
  printf("</table>\n")
}
