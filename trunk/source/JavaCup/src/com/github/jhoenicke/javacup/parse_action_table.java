
package com.github.jhoenicke.javacup;

import java.util.BitSet;
import java.util.TreeSet;

/** This class represents the complete "action" table of the parser. 
 *  It has one row for each state in the parse machine, and a column for
 *  each terminal symbol.  Each entry in the table represents a shift,
 *  reduce, or an error.  
 *  
 *  An error action is represented by 0 (ERROR), a shift action by
 *  odd numbers, i.e. 2*to_state.index() + SHIFT, and a reduce action
 *  by positive even numbers, i.e. 2*prod.index() + REDUCE.
 *  You can use the static function action, isReduce, isShift and index
 *  to manipulate action codes. 
 *
 * @author  Scott Hudson, Jochen Hoenicke
 */
public class parse_action_table {

  /** Actual array of rows, one per state. */
  public final int[][] table;
  
  /** Constant for action type -- error action. */
  public static final int ERROR = 0;

  /** Constant for action type -- shift action. */
  public static final int SHIFT = 1;

  /** Constants for action type -- reduce action. */
  public static final int REDUCE = 2;
  
  /*-----------------------------------------------------------*/
  /*--- Constructor(s) ----------------------------------------*/
  /*-----------------------------------------------------------*/

  /** Simple constructor.  All terminals, non-terminals, and productions must 
   *  already have been entered, and the viable prefix recognizer should
   *  have been constructed before this is called.
   */
  public parse_action_table(Grammar grammar)
    {
      /* determine how many states we are working with */
      int _num_states = grammar.lalr_states().size();
      int _num_terminals = grammar.num_terminals();

      /* allocate the array and fill it in with empty rows */
      table = new int[_num_states][_num_terminals+1];
    }

  /*-----------------------------------------------------------*/
  /*--- General Methods ---------------------------------------*/
  /*-----------------------------------------------------------*/
  /**
   * Returns the action code for the given kind and index.
   * @param kind the kind of the action: ERROR, SHIFT or REDUCE.
   * @param index the index of the destination state resp. production rule.
   */
  public static int action(int kind, int index)
    {
      return 2*index + kind;
    }
  /**
   * Returns true if the code represent a reduce action
   * @param code the action code.
   * @return true for reduce actions.
   */
  public static boolean isReduce(int code)
    {
      return code != 0 && (code & 1) == 0;
    }
  /**
   * Returns true if the code represent a shift action
   * @param code the action code.
   * @return true for shift actions.
   */
  public static boolean isShift(int code)
    {
      return (code & 1) != 0;
    }
  /**
   * Returns the index of the destination state of SHIFT resp. 
   * reduction rule of REDUCE actions.
   * @param code the action code.
   * @return the index.
   */
  public static int index(int code)
    {
      return ((code-1) >> 1);
    }
  
  public static String toString(int code)
    {
      if (code == ERROR)
	return "ERROR";
      else if (isShift(code))
	return "SHIFT("+index(code)+")";
      else
	return "REDUCE("+index(code)+")";
    }
  
  /**
   * Compress the action table into it's runtime form.  This returns
   * an array act_tab and initializes base_table, such that for all
   * entries with table[state][term] != default/error: <pre>
   * act_tab[base_table[state]+2*term] == state
   * act_tab[base_table[state]+2*term+1] == table[state][term]
   * </pre>
   * For all entries that equal default_action[state], we have: <pre>
   * act_tab[base_table[state]+2*term] != state
   * act_tab[state] == default_action[state]
   * </pre>
   */
  public short[] compress(int[] base_table)
    {
      int[] default_actions = new int[table.length];
      TreeSet<CombRow> rows = new TreeSet<CombRow>();
      for (int i = 0; i < table.length; i++)
	{
	  int[] row = table[i];
	  default_actions[i] = row[row.length-1];
	  int len = 0;
	  for (int j = 0; j < row.length-1; j++) 
	    if (row[j] != default_actions[i]) 
	      len++;
	  if (len == 0)
	    continue;

	  int[] comb = new int[len];
	  len = 0;
	  for (int j = 0; j < row.length-1; j++)
	    if (row[j] != default_actions[i])
	      comb[len++] = j;
	  rows.add(new CombRow(i, comb));
	}
      
      BitSet used = new BitSet();
      int combsize = 0;
      for (CombRow row : rows) 
	{
	  row.fitInComb(used);
	  int lastidx = row.base + table[row.index].length; 
	  if (lastidx > combsize)
	    combsize = lastidx;
	}
	
      int _num_states = table.length;
      short[] compressed = new short[_num_states + 2*(combsize)];
      /* Fill default actions */
      for (int i = 0; i < _num_states; i++)
	{
	  base_table[i] = (short) _num_states;
	  compressed[i] = (short) default_actions[i];
	}
      /* Mark entries in comb as invalid */
      for (int i = 0; i < combsize; i++)
	{
	  compressed[_num_states+2*i] = (short) _num_states;
	  compressed[_num_states+2*i+1] = 1;
	}
      for (CombRow row : rows)
	{
	  int base = table.length + 2 * row.base;
	  base_table[row.index] = base;
	  for (int j = 0; j < row.comb.length; j++)
	    {
	      int t = row.comb[j];
	      compressed[base+2*t] = (short) row.index;
	      compressed[base+2*t+1] = (short) table[row.index][t];
	    }
	}
      return compressed;
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Convert to a string. */
  public String toString()
    {
      StringBuilder result = new StringBuilder();
      int cnt;

      result.append("-------- ACTION_TABLE --------\n");
      for (int row = 0; row < table.length; row++)
	{
	  result.append("From state #").append(row).append("\n");
	  cnt = 0;
	  int default_act = table[row][table[row].length-1];
	  result.append(" [default:").append(toString(default_act))
	  	.append("]\n");
	  for (int col = 0; col < table[row].length; col++)
	    {
	      /* if the action is not the default, print it */ 
	      if (table[row][col] != default_act)
		{
		  result.append(" [term ").append(col).append(":")
		    .append(toString(table[row][col])).append("]");

		  /* end the line after the 2nd one */
		  cnt++;
		  if (cnt == 2)
		    {
		      result.append("\n");
		      cnt = 0;
		    }
		}
	    }
          /* finish the line if we haven't just done that */
	  if (cnt != 0) result.append("\n");
	}
      result.append("------------------------------");

      return result.toString();
    }

  /*-----------------------------------------------------------*/

}
