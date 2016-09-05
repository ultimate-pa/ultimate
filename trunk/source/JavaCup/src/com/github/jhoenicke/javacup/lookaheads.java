package com.github.jhoenicke.javacup;

import java.util.ArrayList;
import java.util.Stack;

/**
 * A lookaheads object represents a set of terminal symbols that are
 * used as follower set for a production, to determine under which lookahead
 * symbols that production can be reduced.  Since the lookahead symbols can
 * be directly inherited to other productions, we allow adding listeners
 * to this set, that will be updated whenever this set gets new lookahead
 * symbols.
 * 
 * @author hoenicke
 *
 */
public class lookaheads extends terminal_set {
  private ArrayList<lookaheads> _listeners;
  
  public lookaheads(terminal_set t)
    {
      super(t);
      _listeners = new ArrayList<lookaheads>();
    }

  /** Add a listener object for propagations.  Whenever this object
      changes by adding new lookaheads, all propagation listeners
      will also be updated.
      @param child the lookaheads object that is dependent on this.
   */
  public void add_listener(lookaheads child)
    {
      _listeners.add(child); 
    }

  private boolean add_without_prop(terminal_set new_lookaheads)
    {
      return super.add(new_lookaheads);
    }
  
  /** Adds new lookaheads.  This will also propagate the lookaheads 
      to all objects added by add_propagation().
      @param new_lookaheads  A set of new lookahead symbols.
   */
  public boolean add(terminal_set new_lookaheads)
    {
      if (!super.add(new_lookaheads))
	return false;
      
      Stack<lookaheads> work = new Stack<lookaheads>();
      work.addAll(_listeners);
      while (!work.isEmpty())
	{
	  lookaheads la = work.pop();
	  if (la.add_without_prop(new_lookaheads))
	    {
	      work.addAll(la._listeners);
	    }
	}
      return true;
    }
}
