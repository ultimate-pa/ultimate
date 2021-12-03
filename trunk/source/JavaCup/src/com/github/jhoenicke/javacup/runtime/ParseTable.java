package com.github.jhoenicke.javacup.runtime;

/**
 * Class to hold the action, reduce, and production tables needed by the parser.
 * 
 * @author hoenicke
 */
public final class ParseTable {
  private int[] base_table; 
  private short[] action_table; 
  private short[] reduce_table; 
  private short[] production_table; 

  public ParseTable(String[] tables) 
    {
      TableDecoder decoder = new TableDecoder(tables);
      production_table = decoder.decodeShortArray();
      base_table = decoder.decodeIntArray();
      action_table = decoder.decodeShortArray();
      reduce_table = decoder.decodeShortArray();
    }

  /** Fetch an action from the action table.    
   *
   * @param state the state index of the action being accessed.
   * @param sym   the Symbol index of the action being accessed.
   */
  final short getAction(int state, int sym)
    {
      int base = base_table[state]+2*sym;
      if (action_table[base] == state)
        return action_table[base + 1];
      /* no entry; return default */
      return action_table[state];
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Fetch a state from the reduce-goto table.    
   *
   * @param state the state index of the entry being accessed.
   * @param sym   the Symbol index of the entry being accessed.
   */
  final short getReduce(int state, int sym)
    {
      return reduce_table[reduce_table[state]+sym];
    }

  /** Get the symbol that a production produces.
   *
   * @param rule the rule number (value in action table).
   */
  final int getProductionSymbol(int rule)
    {
      return production_table[2 * rule];
    }

  /** Get the number of tokens a production removes from the stack.
   *
   * @param rule the rule number (value in action table).
   */
  final int getProductionSize(int rule)
    {
      return production_table[2 * rule + 1];
    }
}
