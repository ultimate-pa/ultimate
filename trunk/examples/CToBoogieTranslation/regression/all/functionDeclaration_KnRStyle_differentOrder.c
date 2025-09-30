// Modified version of the program in https://github.com/ultimate-pa/ultimate/issues/528

int tabsize;


static void
indent (from, to, dummy)
     int dummy, from;
     int to;
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
    indent(ndet(), ndet(), ndet());
}

