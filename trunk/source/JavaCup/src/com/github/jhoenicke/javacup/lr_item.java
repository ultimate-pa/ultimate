
package com.github.jhoenicke.javacup;

/** An LR item consisting of a production and the position
 *  of a marker (the "dot") within the production.  Typically item cores 
 *  are written using a production with an embedded "dot" to indicate their 
 *  position.  For example: <pre>
 *     A ::= B * C d E
 *  </pre>
 *  This represents a point in a parse where the parser is trying to match
 *  the given production, and has succeeded in matching everything before the 
 *  "dot" (and hence is expecting to see the symbols after the dot next).  
 *  See lalr_state for full details on the meaning 
 *  and use of items.
 *
 * @see     com.github.jhoenicke.javacup.lalr_state
 * @author  Scott Hudson
*/

public class lr_item implements Comparable<lr_item> {

  /** The production for the item. */
  public final production the_production;

  /** The position of the "dot" -- this indicates the part of the production 
   *  that the marker is before, so 0 indicates a dot at the beginning of 
   *  the RHS.
   */
  public final int dot_pos;

  /**
   * The shifted item.  This is generated when shift_item() is first called.
   */
  private lr_item _shifted;
  
  /*-----------------------------------------------------------*/
  /*--- Constructor(s) ----------------------------------------*/
  /*-----------------------------------------------------------*/

  /** Full constructor.  Is only called by shift_item() and other constructor.
   * @param prod production this item uses.
   * @param pos  position of the "dot" within the item.
   */
  private lr_item(production prod, int pos)
    {
      assert prod != null: "Attempt to create an lr_item_core with a null production";

      the_production = prod;

      assert pos >= 0 && pos <= the_production.rhs_length():
	  "Attempt to create an lr_item_core with a bad dot position";

      dot_pos = pos;
    } 

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Constructor for dot at start of right hand side.  Is only
   * called once for each production from production.item().
   * @param prod production this item uses.
   */
  lr_item(production prod)
    {
      this(prod,0);
    }

  /*-----------------------------------------------------------*/
  /*--- (Access to) Instance Variables ------------------------*/
  /*-----------------------------------------------------------*/

  /** Is the dot at the end of the production? */
  public final boolean dot_at_end() 
    {
       return dot_pos >= the_production.rhs_length();
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Return the symbol after the dot.  If there is no symbol after the dot
   *  we return null. */
  public final symbol symbol_after_dot()
    {
      if (dot_pos < the_production.rhs_length())
	{
	  return the_production.rhs(dot_pos).the_symbol;
	}
      return null;
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Determine if we have a dot before a non terminal, and if so which one 
   *  (return null or the non terminal). 
   */
  public non_terminal dot_before_nt()
    {
      symbol sym;

      /* get the symbol after the dot */
      sym = symbol_after_dot();

      /* if it exists and is a non terminal, return it */
      if (sym instanceof non_terminal)
	return (non_terminal)sym;
      else
	return null;
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Get the lr_item_core that results from shifting the dot one 
   *  position to the right. 
   */
  public lr_item shift_item()
    {
      assert !dot_at_end() : 
	  "Attempt to shift past end of an lr_item";

      if (_shifted == null)
	_shifted = new lr_item(the_production, dot_pos+1);
      return _shifted;
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/
  
  /**
   * Compare two items.  They are compared by index of production_rule first.
   * If productions are the same, they are compared by dot position.
   */
  public int compareTo(lr_item item)
    {
      if (the_production != item.the_production)
	return the_production.index() - item.the_production.index();
      return dot_pos - item.dot_pos;
    }

  /** Convert to a string.
   */
  public String toString()
    {
      StringBuilder result = new StringBuilder();
      result.append(the_production.lhs().name());
      result.append(" ::= ");

      for (int i = 0; i<the_production.rhs_length(); i++)
	{
	  /* do we need the dot before this one? */
	  if (i == dot_pos)
	    result.append("(*) ");
	  
	  /* print the name of the part */
	  result.append(the_production.rhs(i).the_symbol.name())
	  	.append(" ");
	}

      /* put the dot after if needed */
      if (dot_pos == the_production.rhs_length())
	result.append("(*) ");

      return result.toString();
    }

  /*-----------------------------------------------------------*/

  /** Calculate lookahead representing symbols that could appear after the
   *   symbol that the dot is currently in front of.  Note: this routine must
   *   not be invoked before first sets and nullability has been calculated
   *   for all non terminals. 
   */ 
  public terminal_set calc_lookahead(Grammar grammar) 
    {
      /* start with an empty result */
      terminal_set result = new terminal_set(grammar);

      /* consider all nullable symbols after the one to the right of the dot */
      for (int pos = dot_pos; pos < the_production.rhs_length(); pos++) 
  	{
  	   symbol sym = the_production.rhs(pos).the_symbol;

  	   /* if its a terminal add it in and we are done */
  	   if (!sym.is_non_term())
  	     {
  	       result.add((terminal)sym);
  	       break;
  	     }
  	   else
  	     {
  	       non_terminal nt = (non_terminal) sym;
  	       /* otherwise add in first set of the non terminal */
  	       result.add(nt.first_set());

  	       /* if its nullable we continue adding, if not, we are done */
  	       if (!nt.nullable())
  		 break;
  	     }
  	}
      return result;
    }
  
  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Determine if everything from the symbol one beyond the dot all the 
   *  way to the  end of the right hand side is nullable.  This would indicate
   *  that the lookahead of this item must be included in the lookaheads of
   *  all items produced as a closure of this item.  Note: this routine should 
   *  not be invoked until after first sets and nullability have been 
   *  calculated for all non terminals. 
   */
  public boolean is_nullable()
    {
      /* walk down the rhs and bail if we get a non-nullable symbol */
      for (int pos = dot_pos; pos < the_production.rhs_length(); pos++)
  	{
  	  symbol sym = the_production.rhs(pos).the_symbol;

  	  /* if its a terminal we fail */
  	  if (!sym.is_non_term()) return false;

  	  /* if its not nullable we fail */
  	  if (!((non_terminal)sym).nullable()) return false;
  	}

      /* if we get here its all nullable */
      return true;
    }    
}