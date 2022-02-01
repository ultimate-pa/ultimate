package com.github.jhoenicke.javacup;

import java.util.BitSet;

public class CombRow implements Comparable<CombRow> {
  public final int   index;
  public final int[] comb;
  public final int   width;
  public int         base;

  public CombRow(int index, int[] comb)
    {
      this.index = index;
      this.width = comb[comb.length-1] - comb[0] + 1;
      this.comb = comb;
    }

  /**
   * Compares this comb with another comb.
   * Combs are ordered by decreasing size and then by index.  This
   * ordering ensures that large combs, which are hardest to fit, come
   * first.
   * @param other the other comb.
   * @return negative if smaller, positive if larger than other comb.
   */
  public int compareTo(CombRow other)
    {
      if (width != other.width)
	return other.width - width;
      if (comb.length != other.comb.length)
	return other.comb.length - comb.length;
      if (comb[comb.length-1] != other.comb[other.comb.length-1])
	return comb[comb.length-1] - other.comb[other.comb.length-1];
      return other.index - index;
      //return index - other.index;
    }

  /**
   * Fit this comb into a bit set.  This computes the base offset
   * such that all entries in the bit set for this comb are free.
   * It updates the bit set to mark these entries as used.
   * @param used the bit set of used entries.
   */
  public void fitInComb(BitSet used)
    {
      next_base:
	for (int base = 0; true; base++)
	  {
	    for (int j = 0; j < comb.length; j++)
	      {
		if (used.get(base+comb[j]))
		  continue next_base;
	      }

	    for (int j = 0; j < comb.length; j++)
	      used.set(base+comb[j]);

	    this.base = base;
	    return;
	  }
    }
}
