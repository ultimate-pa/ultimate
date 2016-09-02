package com.github.jhoenicke.javacup.runtime;

/**
 * Auxiliary class to decode a bunch of strings into integer and short arrays storing the
 * action and reduce tables.
 * 
 * @author hoenicke
 */
final class TableDecoder {
  private String[] coded_tables;
  private int array_idx;
  private int string_idx;
  
  public TableDecoder(String[] tables) 
    {
      this.coded_tables = tables;
      array_idx = string_idx = 0;
    }
  
  private char advance()
    {
      if (string_idx == coded_tables[array_idx].length())
	{
	  string_idx = 0;
	  array_idx++;
	}
      return coded_tables[array_idx].charAt(string_idx++);
    }
  
  public short decodeShort()
    {
      return (short) advance();
    }
  
  public int decodeInt()
    {
      int val = advance();
      if (val >= 0x8000)
	val = ((val & 0x7fff)<<16) + advance();
      return val;
    }
  
  public int[] decodeIntArray() 
    {
      int size = decodeInt();
      int[] arr = new int[size];
      for (int i = 0; i < size; i++)
	arr[i] = decodeInt();
      return arr;
    }

  public short[] decodeShortArray() 
    {
      int size = decodeInt();
      short[] arr = new short[size];
      for (int i = 0; i < size; i++)
	arr[i] = decodeShort();
      return arr;
    }
}
