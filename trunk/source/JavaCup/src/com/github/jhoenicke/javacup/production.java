package com.github.jhoenicke.javacup;

/**
 * This class represents a production in the grammar. It contains a LHS non
 * terminal, and an array of RHS symbols. As various transformations are done on
 * the RHS of the production, it may shrink. As a result a separate length is
 * always maintained to indicate how much of the RHS array is still valid.
 * <p>
 * 
 * I addition to construction and manipulation operations, productions provide
 * methods for factoring out actions (see remove_embedded_actions()), for
 * computing the nullability of the production (i.e., can it derive the empty
 * string, see check_nullable()), and operations for computing its first set
 * (i.e., the set of terminals that could appear at the beginning of some string
 * derived from the production, see check_first_set()).
 * 
 * @see com.github.jhoenicke.javacup.production_part
 * @see com.github.jhoenicke.javacup.symbol_part
 * @see com.github.jhoenicke.javacup.action_part
 * @version last updated: 7/3/96
 * @author Frank Flannery
 */

public class production {

  /*-----------------------------------------------------------*/
  /*--- Constructor(s) ----------------------------------------*/
  /*-----------------------------------------------------------*/

  /**
   * Full constructor. This constructor accepts a LHS non terminal, an array of
   * RHS parts (including terminals, non terminals, and actions), and a string
   * for a final reduce action. It does several manipulations in the process of
   * creating a production object. After some validity checking it translates
   * labels that appear in actions into code for accessing objects on the
   * runtime parse stack. It them merges adjacent actions if they appear and
   * moves any trailing action into the final reduce actions string. Next it
   * removes any embedded actions by factoring them out with new action
   * productions. Finally it assigns a unique index to the production.
   * <p>
   * 
   * Factoring out of actions is accomplished by creating new "hidden" non
   * terminals. For example if the production was originally:
   * 
   * <pre>
   *    A ::= B {action} C D
   * </pre>
   * 
   * then it is factored into two productions:
   * 
   * <pre>
   *    A ::= B X C D
   *    X ::= {action}
   * </pre>
   * 
   * (where X is a unique new non terminal). This has the effect of placing all
   * actions at the end where they can be handled as part of a reduce by the
   * parser.
   */
  public production(int index, int action_index, non_terminal lhs_sym, symbol_part rhs[], 
      	int last_act_loc, action_part action, terminal precedence)
    {
      if (precedence != null)
	{
	  _rhs_prec = precedence.precedence_num();
	  _rhs_assoc = precedence.precedence_side();
	}
      _lhs = lhs_sym;
      _rhs = rhs;
      _action = action;
      _index = index;
      _action_index = action_index;
      for (int i = 0; i < rhs.length; i++)
	{
	  symbol rhs_sym = rhs[i].the_symbol;
	  rhs_sym.note_use();
	  if (precedence == null && rhs_sym instanceof terminal)
	    {
	      terminal term = (terminal) rhs_sym;
	      if (term.precedence_num() != assoc.no_prec)
		{
		  if (_rhs_prec == assoc.no_prec)
		    {
		      _rhs_prec = term.precedence_num();
		      _rhs_assoc = term.precedence_side();
		    }
		  else if (term.precedence_num() != _rhs_prec)
		    {
		      ErrorManager.getManager().emit_error("Production "+this+
		      " has more than one precedence symbol");
		    }
		}
	    }
	}
      indexOfIntermediateResult = last_act_loc;
      /* put us in the production list of the lhs non terminal */
      lhs_sym.add_production(this);
    }

  /*-----------------------------------------------------------*/
  /*--- (Access to) Instance Variables ------------------------*/
  /*-----------------------------------------------------------*/

  /** The left hand side non-terminal. */
  private final non_terminal _lhs;

  /** The left hand side non-terminal. */
  public non_terminal lhs()
    {
      return _lhs;
    }

  /** The precedence of the rule */
  private int _rhs_prec = -1;
  private int _rhs_assoc = -1;

  /** Access to the precedence of the rule */
  public int precedence_num()
    {
      return _rhs_prec;
    }

  public int precedence_side()
    {
      return _rhs_assoc;
    }

  /* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . */

  /** A collection of parts for the right hand side. */
  private final symbol_part _rhs[];

  /** Access to the collection of parts for the right hand side. */
  public symbol_part rhs(int indx)
    {
      return _rhs[indx];
    }

  /* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . */

  /** How much of the right hand side array we are presently using. */
  public int rhs_length()
    {
      return _rhs.length;
    }

  public int rhs_stackdepth() 
    {
      return _rhs.length;
    }

  /* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . */

  /**
   * An action_part containing code for the action to be performed when we
   * reduce with this production.
   */
  private final action_part _action;

  /**
   * An action_part containing code for the action to be performed when we
   * reduce with this production.
   */
  public action_part action()
    {
      return _action;
    }

  /* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . */

  /** Index number of the production. */
  private final int _index, _action_index;

  /** Index number of the production. */
  public int index()
    {
      return _index;
    }

  /** Index number of the action for this production. */
  public int action_index()
    {
      return _action_index;
    }

  /* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . */

  /** initial lr item corresponding to the production. */
  private lr_item _itm;

  /** Index number of the production. */
  public lr_item item()
    {
      if (_itm == null)
	_itm = new lr_item(this);
      return _itm;
    }

  /* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . */

  /** Is the nullability of the production known or unknown? */
  private boolean _nullable_known = false;

  /** Nullability of the production (can it derive the empty string). */
  private boolean _nullable = false;

  /* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . */

  /*-----------------------------------------------------------*/
  /*--- General Methods ---------------------------------------*/
  /*-----------------------------------------------------------*/

  private int indexOfIntermediateResult;
  /**
   * @return the index of the result of the previous intermediate action on the stack relative to top, -1 if no previous action
   */
  public int getIndexOfIntermediateResult(){
      return indexOfIntermediateResult;
  }
  
  /* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . */

  /**
   * Check to see if the production (now) appears to be nullable. A production
   * is nullable if its RHS could derive the empty string. This results when the
   * RHS is empty or contains only non terminals which themselves are nullable.
   */
  public boolean check_nullable()
    {
      /* if we already know bail out early */
      if (_nullable_known)
	return _nullable;

      /* if we have a zero size RHS we are directly nullable */
      if (rhs_length() == 0)
	{
	  /* stash and return the result */
	  return set_nullable(true);
	}

      /* otherwise we need to test all of our parts */
      for (int pos = 0; pos < rhs_length(); pos++)
	{
	  /* only look at non-actions */
	  symbol sym = _rhs[pos].the_symbol;

	  /* if its a terminal we are definitely not nullable */
	  if (!sym.is_non_term())
	    return set_nullable(false);
	  /* its a non-term, is it marked nullable */
	  else if (!((non_terminal) sym).nullable())
	    /* this one not (yet) nullable, so we aren't */
	    return false;
	}

      /* if we make it here all parts are nullable */
      return set_nullable(true);
    }

  /** set (and return) nullability */
  private boolean set_nullable(boolean v)
    {
      _nullable_known = true;
      _nullable = v;
      return v;
    }
  
  public boolean is_proxy()
    {
      return _rhs.length == 1 && action() == null;
    }

  /* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . */

  /**
   * Return the first set based on current NT firsts. This assumes
   * that nullability has already been computed for all non terminals and
   * productions.
   */
  public terminal_set first_set(Grammar grammar)
    {
      return item().calc_lookahead(grammar);
    }

  /* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . */

  /** Convert to a simpler string. */
  public String toString()
    {
      StringBuilder result = new StringBuilder();

      result.append(lhs().name()).append(" ::= ");
      for (int i = 0; i < rhs_length(); i++)
	result.append(rhs(i).the_symbol.name()).append(" ");

      return result.toString();
    }

  /*-----------------------------------------------------------*/

}
