package com.github.jhoenicke.javacup;

/**
 * This class represents a transition in an LALR viable prefix recognition
 * machine. Transitions can be under terminals or non-terminals. They are
 * internally linked together into singly linked lists containing all the
 * transitions out of a single state via the next field.
 * 
 * @see com.github.jhoenicke.javacup.lalr_state
 * @version last updated: 11/25/95
 * @author Scott Hudson
 * 
 */
public class lalr_transition {
  
  /** The symbol we make the transition on. */
  public final symbol on_symbol;

  /** The state we transition to. */
  public final lalr_state to_state;

  /** Next transition in linked list of transitions out of a state */
  public final lalr_transition next;

  /*-----------------------------------------------------------*/
  /*--- Constructor(s) ----------------------------------------*/
  /*-----------------------------------------------------------*/

  /**
   * Full constructor.
   * 
   * @param on_sym
   *                symbol we are transitioning on.
   * @param to_st
   *                state we transition to.
   * @param nxt
   *                next transition in linked list.
   */
  public lalr_transition(symbol on_sym, lalr_state to_st, lalr_transition nxt)
    {
      /* sanity checks */
      assert on_sym != null : "Attempt to create transition on null symbol";
      assert to_st != null : "Attempt to create transition to null state";

      /* initialize */
      on_symbol = on_sym;
      to_state = to_st;
      next = nxt;
    }

  /* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . */

  /** Convert to a string. */
  public String toString()
    {
      return "transition on " + on_symbol.name() + " to state ["
	  + to_state.index() + "]";
    }
}
