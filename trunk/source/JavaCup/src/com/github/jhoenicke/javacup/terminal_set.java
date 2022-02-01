
package com.github.jhoenicke.javacup;

/** A set of terminals implemented as a bitset. 
 * @version last updated: 2008-11-08
 * @author  Scott Hudson, Jochen Hoenicke
 */
public class terminal_set {
  private final static int LOG_BITS_PER_UNIT = 6;
  private final static int BITS_PER_UNIT = 64;
  private long[] _elements;
  private Grammar _grammar;

  /*-----------------------------------------------------------*/
  /*--- Constructor(s) ----------------------------------------*/
  /*-----------------------------------------------------------*/

  /** Constructor for an empty set. */
  public terminal_set(Grammar g) 
    { 
      /* allocate the bitset at what is probably the right size */
      _grammar = g;
      _elements = new long[((g.num_terminals()-1) >>> LOG_BITS_PER_UNIT)+1];
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Constructor for cloning from another set. 
   * @param other the set we are cloning from.
   */
  public terminal_set(terminal_set other) 
    {
      this (other._grammar);
      _elements = other._elements.clone();
    }

  /*-----------------------------------------------------------*/
  /*--- General Methods ----------------------------------------*/
  /*-----------------------------------------------------------*/

  /** Determine if the set is empty. */
  public boolean empty()
    {
      for (int i = 0; i < _elements.length; i++)
	if (_elements[i] != 0)
	  return false;
      return true;
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Determine if the set contains a particular terminal. 
   * @param sym the terminal symbol we are looking for.
   */
  public boolean contains(terminal sym) 
    {
      return contains(sym.index());
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Given its index determine if the set contains a particular terminal. 
   * @param indx the index of the terminal in question.
   */
  public boolean contains(int indx) 
    {
      int idx  = indx >> LOG_BITS_PER_UNIT;
      long mask = (1L << (indx & (BITS_PER_UNIT-1)));
      return (_elements[idx] & mask) != 0;
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Determine if this set is an (improper) subset of another.
   * @param other the set we are testing against.
   */
  public boolean is_subset_of(terminal_set other)
    {
      assert(other._elements.length == _elements.length);
      for (int i = 0; i < _elements.length; i++)
	if ((_elements[i] & ~other._elements[i]) != 0)
	  return false;
      return true;
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Add a single terminal to the set.  
   * @param sym the terminal being added.
   * @return true if this changes the set.
   */
  public boolean add(terminal sym) 
    {
      int indx = sym.index();
      int idx  = indx >> LOG_BITS_PER_UNIT;
      long mask = (1L << (indx & (BITS_PER_UNIT-1)));
      boolean result = (_elements[idx] & mask) == 0;
      _elements[idx] |= mask;
      return result;
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Remove a terminal if it is in the set.
   * @param sym the terminal being removed.
   */
  public void remove(terminal sym) 
    {
      int indx = sym.index();
      int idx  = indx >> LOG_BITS_PER_UNIT;
      long mask = (1L << (indx & (BITS_PER_UNIT-1)));
      _elements[idx] &= ~mask;
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Add (union) in a complete set.  
   * @param other the set being added.
   * @return true if this changes the set.
   */
  public boolean add(terminal_set other)
    {
      assert(other._elements.length == _elements.length);
      boolean changed = false;
      for (int i = 0; i < _elements.length; i++)
	{
	  if ((~_elements[i] & other._elements[i]) != 0)
	    changed = true;
	  _elements[i] |= other._elements[i];
	}
      return changed;
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Determine if this set intersects another.
   * @param other the other set in question.
   */
   public boolean intersects(terminal_set other)
     {
       assert(other._elements.length == _elements.length);
       for (int i = 0; i < _elements.length; i++)
 	{
 	  if ((_elements[i] & other._elements[i]) != 0)
 	    return true;
 	}
       return false;
     }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Equality comparison. */
  public boolean equals(terminal_set other)
    {
      assert(other._elements.length == _elements.length);
      for (int i = 0; i < _elements.length; i++)
	{
	  if (_elements[i] != other._elements[i])
	    return false;
	}
      return true;
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Generic equality comparison. */
  public boolean equals(Object other)
    {
      if (!(other instanceof terminal_set))
	return false;
      else
	return equals((terminal_set)other);
    }
  
  @Override
  public int hashCode() 
    {
      int hash = 0;
      for (int i = 0; i < _elements.length; i++)
	hash = 13*hash + 157*(int)(_elements[i] >>16) + (int)_elements[i];
      return hash;
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Convert to string. */
  public String toString()
    {
      StringBuilder result = new StringBuilder("{");
      String comma = "";
      for (int t = 0; t < _grammar.num_terminals(); t++)
	{
	  if (contains(t))
	    {
	      result.append(comma).append(_grammar.get_terminal(t));
	      comma = ", ";
	    }
	}
      result.append("}");
      return result.toString();
    }

  /*-----------------------------------------------------------*/

}

