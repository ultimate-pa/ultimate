
package com.github.jhoenicke.javacup;

import java.util.ArrayList;
import java.util.Map;
import java.util.Stack;
import java.util.TreeMap;
import java.util.Map.Entry;

/** This class represents a state in the LALR viable prefix recognition machine.
 *  A state consists of a mapping from LR items to a set of terminals (lookaheads)
 *  and of transitions to other states under terminal and non-terminal symbols.
 *  Each state represents a potential configuration of the parser.  If the item 
 *  set of a state includes an item such as: <pre>
 *    [A ::= B * C d E , {a,b,c}]
 *  </pre> 
 *  this indicates that when the parser is in this state it is currently 
 *  looking for an A of the given form, has already seen the B, and would
 *  expect to see an a, b, or c after this sequence is complete.  Note that
 *  the parser is normally looking for several things at once (represented
 *  by several items).  In our example above, the state would also include
 *  items such as: <pre>
 *    [C ::= * X e Z, {d}]
 *    [X ::= * f, {e}]
 *  </pre> 
 *  to indicate that it was currently looking for a C followed by a d (which
 *  would be reduced into a C, matching the first symbol in our production 
 *  above), and the terminal f followed by e.
 *
 *  <p>At runtime, the parser uses a viable prefix recognition machine made up
 *  of these states to parse.  The parser has two operations, shift and reduce.
 *  In a shift, it consumes one Symbol and makes a transition to a new state.
 *  This corresponds to "moving the dot past" a terminal in one or more items
 *  in the state (these new shifted items will then be found in the state at
 *  the end of the transition).  For a reduce operation, the parser is 
 *  signifying that it is recognizing the RHS of some production.  To do this
 *  it first "backs up" by popping a stack of previously saved states.  It 
 *  pops off the same number of states as are found in the RHS of the 
 *  production.  This leaves the machine in the same state is was in when the
 *  parser first attempted to find the RHS.  From this state it makes a 
 *  transition based on the non-terminal on the LHS of the production.  This
 *  corresponds to placing the parse in a configuration equivalent to having 
 *  replaced all the symbols from the the input corresponding to the RHS with 
 *  the symbol on the LHS.</p>
 *
 * @see     com.github.jhoenicke.javacup.lr_item
 * @see     com.github.jhoenicke.javacup.lalr_transition
 * @version last updated: 7/3/96
 * @author  Frank Flannery
 *  
 */

public class lalr_state {
  /*-----------------------------------------------------------*/
  /*--- Constructor(s) ----------------------------------------*/
  /*-----------------------------------------------------------*/

  /** Constructor for building a state from a set of items.
   * @param kernel the set of items that makes up the kernel of this state.
   * @param index  a unique index that is given to this state.
   */
  public lalr_state(Map<lr_item, terminal_set> kernel, int index)
   {
     /* don't allow null or duplicate item sets */
     if (kernel == null)
       throw new AssertionError(
	 "Attempt to construct an LALR state from a null item set");

     /* assign a unique index */
      _index = index;

     /* store the items */
     _items = new TreeMap<lr_item, lookaheads>();
     for (Entry<lr_item, terminal_set> entry : kernel.entrySet())
       _items.put(entry.getKey(), new lookaheads(entry.getValue()));
   }
  
 /*-----------------------------------------------------------*/
  /*--- (Access to) Instance Variables ------------------------*/
  /*-----------------------------------------------------------*/

  /** The item set for this state. */
  private TreeMap<lr_item, lookaheads> _items;

  /** The item set for this state. */
  public TreeMap<lr_item, lookaheads> items() {return _items;}

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** List of transitions out of this state. */
  private lalr_transition _transitions = null;

  /** Index of this state in the parse tables */
  private int _index;

  /** Index of this state in the parse tables */
  public int index() {return _index;}

  /*-----------------------------------------------------------*/
  /*--- General Methods ---------------------------------------*/
  /*-----------------------------------------------------------*/

  /** Compute the closure of the set using the LALR closure rules.  Basically
   *  for every item of the form: <pre>
   *    [L ::= a *N alpha, l] 
   *  </pre>
   *  (where N is a a non terminal and alpha is a string of symbols) make 
   *  sure there are also items of the form:  <pre>
   *    [N ::= *beta, first(alpha l)] 
   *  </pre>
   *  corresponding to each production of N.  Items with identical cores but 
   *  differing lookahead sets are merged by creating a new item with the same 
   *  core and the union of the lookahead sets (the LA in LALR stands for 
   *  "lookahead merged" and this is where the merger is).  This routine 
   *  assumes that nullability and first sets have been computed for all 
   *  productions before it is called.
   */
  public void compute_closure(Grammar grammar)
    {
      terminal_set  new_lookaheads;
      boolean       need_prop;

      /* each current element needs to be considered */
      Stack<lr_item> consider = new Stack<lr_item>();
      consider.addAll(_items.keySet());

      /* repeat this until there is nothing else to consider */
      while (consider.size() > 0)
	{
	  /* get one item to consider */
	  lr_item itm = consider.pop();

	  /* do we have a dot before a non terminal */
	  non_terminal nt = itm.dot_before_nt();
	  if (nt != null)
	    {
	      lr_item nextitm = itm.shift_item();
	      /* create the lookahead set based on first symbol after dot */
	      new_lookaheads = nextitm.calc_lookahead(grammar);

	      /* are we going to need to propagate our lookahead to new item */
	      need_prop = nextitm.is_nullable();
	      if (need_prop)
		new_lookaheads.add(_items.get(itm));
	      
	      /* create items for each production of that non term */
	      for (production prod : nt.productions() )
		{
		  /* create new item with dot at start and that lookahead */
		  lr_item new_itm = prod.item();
		  lookaheads new_la;
		  if (_items.containsKey(new_itm))
		    {
		      new_la = _items.get(new_itm); 
		      new_la.add(new_lookaheads);
		    }
		  else
		    {
		      new_la = new lookaheads(new_lookaheads);
		      _items.put(new_itm, new_la);
		      /* that may need further closure, consider it also */ 
		      consider.push(new_itm);
		    }
		  
		  /* if propagation is needed link to that item */
		  if (need_prop)
		    _items.get(itm).add_listener(new_la);
		} 
	    }
	} 
    }
  
  public void compute_successors(Grammar grammar) 
    {
      /* gather up all the symbols that appear before dots */
      TreeMap<symbol, ArrayList<lr_item>> outgoing =
	new TreeMap<symbol, ArrayList<lr_item>>();
      for (lr_item itm : _items.keySet() )
	{
	  /* add the symbol after the dot (if any) to our collection */
	  symbol sym = itm.symbol_after_dot();
	  if (sym != null)
	    {
	      if (!outgoing.containsKey(sym))
		outgoing.put(sym, new ArrayList<lr_item>());
	      outgoing.get(sym).add(itm);
	    }
	}
      
      /* now create a transition out for each individual symbol */
      for (symbol out : outgoing.keySet() )
	{
	  /* gather up shifted versions of all the items that have this
		 symbol before the dot */
	  TreeMap<lr_item, terminal_set> new_items = new TreeMap<lr_item, terminal_set>();

	  /* find proxy symbols on the way */
	  ArrayList<symbol> proxy_symbols = new ArrayList<symbol>();
	  proxy_symbols.add(out);	  
	  for (int i = 0; i < proxy_symbols.size(); i++)
	    {
	      symbol sym = proxy_symbols.get(i);
	      for (lr_item itm : outgoing.get(sym))
		{
		  /* add to the kernel of the new state */
		  if (itm.the_production.is_proxy())
		    {
		      symbol proxy = itm.the_production.lhs();
		      if (!proxy_symbols.contains(proxy))
			{
			  proxy_symbols.add(proxy);
			}
		    }
		  else
		    {
		      new_items.put(itm.shift_item(), items().get(itm));
		    }
		}
	    }

	  /* create/get successor state */
	  lalr_state new_st = grammar.get_lalr_state(new_items);
	  for (symbol sym : proxy_symbols)
	    {
	      for (lr_item itm : outgoing.get(sym))
		{
		  /* ... remember that itm has propagate link to it */
		  if (!itm.the_production.is_proxy())
		    {
		      items().get(itm).add_listener(
			  new_st.items().get(itm.shift_item()));
		    }
		}
	    }

	  /* add a transition from current state to that state */
	  _transitions = new lalr_transition(out, new_st, _transitions);
	}
    }
 
  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Propagate lookahead sets out of this state. This recursively 
   *  propagates to all items that have propagation links from some item 
   *  in this state. 
   */
  public void propagate_lookaheads(Map<lr_item, terminal_set> new_kernel)
    {
      /* Add the new lookaheads to the existing ones.
       * This will propagate the lookaheads to all dependent items.
       */
      for (Entry<lr_item, terminal_set> entry : new_kernel.entrySet())
	{
	  _items.get(entry.getKey()).add(entry.getValue());
	}
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/
  
  /** Fill in the parse table entries for this state.  There are two 
   *  parse tables that encode the viable prefix recognition machine, an 
   *  action table and a reduce-goto table.  The rows in each table 
   *  correspond to states of the machine.  The columns of the action table
   *  are indexed by terminal symbols and correspond to either transitions 
   *  out of the state (shift entries) or reductions from the state to some
   *  previous state saved on the stack (reduce entries).  All entries in the
   *  action table that are not shifts or reduces, represent errors.    The
   *  reduce-goto table is indexed by non terminals and represents transitions 
   *  out of a state on that non-terminal.<p>
   *  Conflicts occur if more than one action needs to go in one entry of the
   *  action table (this cannot happen with the reduce-goto table).  Conflicts
   *  are resolved by always shifting for shift/reduce conflicts and choosing
   *  the lowest numbered production (hence the one that appeared first in
   *  the specification) in reduce/reduce conflicts.  All conflicts are 
   *  reported and if more conflicts are detected than were declared by the
   *  user, code generation is aborted.
   *
   * @param act_table    the action table to put entries in.
   * @param reduce_table the reduce-goto table to put entries in.
   */
  public void build_table_entries(Grammar grammar,
    parse_action_table act_table, 
    parse_reduce_table reduce_table,
    boolean compact_reduces)
    {
      int     act;
      symbol  sym;
      
      int        default_lasize = 0;
      int	 default_action = parse_action_table.ERROR;
      boolean    default_prodisempty = false;

      /* pull out our rows from the tables */
      int[] our_act_row = act_table.table[index()];
      production[] productions = new production[grammar.num_terminals()+1];
      lalr_state[] our_red_row = reduce_table.table[index()];

      /* consider each item in our state */
      for (Entry<lr_item, lookaheads> itm : items().entrySet())
	{
	  /* if its completed (dot at end) then reduce under the lookahead */
	  if (itm.getKey().dot_at_end())
	    {
	      boolean conflict = false;
	      act = parse_action_table.action(parse_action_table.REDUCE,
		  itm.getKey().the_production.action_index());
	      int lasize = 0;

	      /* consider each lookahead symbol */
	      for (int t = 0; t < grammar.num_terminals(); t++)
		{
		  /* skip over the ones not in the lookahead */
		  if (!itm.getValue().contains(t)) continue;
		  lasize++;

	          /* if we don't already have an action put this one in */
	          if (our_act_row[t] == parse_action_table.ERROR)
		    {
	              our_act_row[t] = act;
	              productions[t] = itm.getKey().the_production;
		    }
	          else
		    {
		      /* we now have a reduce/reduce conflict */
		      /* take the other one; it came earlier */
		      conflict = true;
		    }
		}
	      
	      /* if there was a conflict with a different production, report it now.
	       * We can't do it in the above loop since it would call report for every
	       * terminal symbol on which the conflict is.
	       */
	      if (conflict)
		{
		  for (Entry<lr_item,lookaheads> compare : items().entrySet())
		    {
		      /* the compare item must be in a before this item in the entrySet */
		      if (itm.getKey() == compare.getKey())
			break;

		      /* is it a reduce */
		      if (compare.getKey().dot_at_end())
			{
			  if (compare.getValue().intersects(itm.getValue()))
			    /* report a reduce/reduce conflict */
			    grammar.report_reduce_reduce(this, compare, itm);
			}
		    }
		}
	      
	      /* if we compact reduce tables make this action the default
	       * action if it has the most lookahead symbols
	       */
	      if (compact_reduces && lasize > default_lasize) 
		{
		  production prod = itm.getKey().the_production;
		  /* don't make it default if it doesn't save a rule */ 
		  if (prod.rhs_length() != 0 || lasize > 1)
		    {
		      default_prodisempty = prod.rhs_length() == 0;
		      default_lasize = lasize;
		      default_action = act; 
		    }
		}
	    }
	}

      /* consider each outgoing transition */
      for (lalr_transition trans=_transitions; trans!=null; trans=trans.next)
	{
	  /* if its on an terminal add a shift entry */
	  sym = trans.on_symbol;
	  int idx = sym.index();
	  if (!sym.is_non_term())
	    {
	      act = parse_action_table.action
	      	(parse_action_table.SHIFT, trans.to_state.index());
	      /* if we don't already have an action put this one in */
	      if (our_act_row[idx] == parse_action_table.ERROR)
		{
	          our_act_row[sym.index()] = act;
		}
	      else
		{
		  /* this is a shift_reduce conflict */
		  production p = productions[idx];

		  /* check if precedence can fix it */
		  if (!fix_with_precedence(p, (terminal) sym, our_act_row, act))
		    {
		      /* shift always wins */
		      our_act_row[idx] = act;
		      grammar.report_shift_reduce(this, p, sym);
		    }
		}
	    }
	  else
	    {
	      /* for non terminals add an entry to the reduce-goto table */
	      our_red_row[idx] = trans.to_state;
	    }
	}
      
      /* Check if there is already an action for the error symbol.
       * This must be the default action.
       */
      act = our_act_row[terminal.error.index()]; 
      if (act != parse_action_table.ERROR)
	{
	  default_action = parse_action_table.isReduce(act) ? act 
		: parse_action_table.ERROR; 
	  default_prodisempty = false;
	}
      our_act_row[grammar.num_terminals()] = default_action;
      if (default_action != parse_action_table.ERROR)
	{
	  for (int i = 0; i < grammar.num_terminals(); i++)
	    {
	      /* map everything to default action, except the error transition
	       * if default_action reduces an empty production.
	       * The latter may otherwise lead to infinite loops.
	       */
	      if (our_act_row[i] == parse_action_table.ERROR
		  && (i != terminal.error.index() || !default_prodisempty))
		our_act_row[i] = default_action;
	    }
	}
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

    
  /** Procedure that attempts to fix a shift/reduce error by using
   * precedences.  --frankf 6/26/96
   *  
   *  if a production (also called rule) and the lookahead terminal
   *  have a precedence, then the table can be fixed.  if the rule
   *  has greater precedence than the terminal, a reduce by that rule
   *  is inserted in the table.  If the terminal has a higher precedence, 
   *  it is shifted.  if they have equal precedence, then the associativity
   *  of the precedence is used to determine what to put in the table:
   *  if the precedence is left associative, the action is to reduce. 
   *  if the precedence is right associative, the action is to shift.
   *  if the precedence is non associative, then it is a shift/reduce error.
   *
   *  @param p           the production
   *  @param term_index  the index of the lookahead terminal
   *  @param parse_action_row  a row of the action table
   *  @param act         the rule in conflict with the table entry
   */
  private boolean fix_with_precedence(
		        production       p,
			terminal         term,
			int[]            table_row,
			int              shift_act)
    {
      /* if both production and terminal have a precedence number, 
       * it can be fixed */
      if (p.precedence_num() > assoc.no_prec
	  && term.precedence_num() > assoc.no_prec) 
	{

	  int compare = term.precedence_num() - p.precedence_num();
	  if (compare == 0)
	    compare = term.precedence_side() - assoc.nonassoc; 

	  /* if production precedes terminal, keep reduce in table */
	  if (compare < 0)
	    return true;

	  /* if terminal precedes rule, put shift in table */
	  else if (compare > 0)
	    {
	      table_row[term.index()] = shift_act; 
	      return true;
	    } 
	}

      /* otherwise, neither the rule nor the terminal has a precedence,
	 so it can't be fixed. */
      return false;
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Convert to a string. */
  public String toString()
    {
      StringBuilder result = new StringBuilder();
      lalr_transition tr;

      /* dump the item set */
      result.append("lalr_state [").append(index()).append("]: {\n");
      for (Entry<lr_item,lookaheads> itm : items().entrySet()) 
	{
	  /* print the kernel first */
	  if (itm.getKey().dot_pos == 0)
	    continue;
	  result.append("  [").append(itm.getKey()).append(", ");
	  result.append(itm.getValue()).append("]\n");
	}
      for (Entry<lr_item,lookaheads> itm : items().entrySet()) 
	{
	  /* do not print the kernel */
	  if (itm.getKey().dot_pos != 0)
	    continue;
	  result.append("  [").append(itm.getKey()).append(", ");
	  result.append(itm.getValue()).append("]\n");
	}
      result.append("}\n");

      /* dump the transitions */
      for (tr = _transitions; tr != null; tr = tr.next)
	{
	  result.append(tr).append("\n");
	}

      return result.toString();
    }

  /*-----------------------------------------------------------*/
}
