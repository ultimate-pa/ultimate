// See https://github.com/ultimate-pa/ultimate/issues/528

int tabsize;


static void
indent (from, to)
     int from, to;
{
  while (from < to)
    {
      if ((to / tabsize) > (from / tabsize))
    {
      from += tabsize - from % tabsize;
    }
      else
    {
      from++;
    }
    }
}

extern int ndet();

int main()
{
    indent(ndet(), ndet());
}

