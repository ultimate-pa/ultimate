
package com.github.jhoenicke.javacup.runtime;

import java.util.ArrayList;
import java.util.List;

/** This class implements a temporary or "virtual" parse stack that 
 *  replaces the top portion of the actual parse stack (the part that 
 *  has been changed by some set of operations) while maintaining its
 *  original contents.  This data structure is used when the parse needs 
 *  to "parse ahead" to determine if a given error recovery attempt will 
 *  allow the parse to continue far enough to consider it successful.  Once 
 *  success or failure of parse ahead is determined the system then 
 *  reverts to the original parse stack (which has not actually been 
 *  modified).  Since parse ahead does not execute actions, only parse
 *  state is maintained on the virtual stack, not full Symbol objects.
 *
 * @see     com.github.jhoenicke.javacup.runtime.lr_parser
 * @version last updated: 7/3/96
 * @author  Frank Flannery
 */

class VirtualParseStack {
  /*-----------------------------------------------------------*/
  /*--- Constructor(s) ----------------------------------------*/
  /*-----------------------------------------------------------*/

  /** Constructor to build a virtual stack out of a real stack. */
  public VirtualParseStack(List<Symbol> shadowing_stack) throws java.lang.Exception
    {
      /* sanity check */
      if (shadowing_stack == null)
	throw new Exception(
	  "Internal parser error: attempt to create null virtual stack");

      /* set up our internals */
      real_stack = shadowing_stack;
      vstack     = new ArrayList<Integer>();
      real_top   = shadowing_stack.size();
      getFromReal();
    }

  /*-----------------------------------------------------------*/
  /*--- (Access to) Instance Variables ------------------------*/
  /*-----------------------------------------------------------*/
       
  /** The real stack that we shadow.  This is accessed when we move off
   *  the bottom of the virtual portion of the stack, but is always left
   *  unmodified.
   */
  private List<Symbol> real_stack;

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Top of stack indicator for where we leave off in the real stack.
   *  This is measured from bottom of stack, so 0 would indicate that no
   *  elements are left on the real stack.  This points to the element
   *  after the one that needs to be popped from the real stack next. 
   */
  private int real_top;

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** The virtual top portion of the stack.  This stack contains Integer
   *  objects with state numbers.  This stack shadows the top portion
   *  of the real stack within the area that has been modified (via operations
   *  on the virtual stack).  When this portion of the stack becomes empty we 
   *  transfer elements from the underlying stack onto this stack. 
   */
  private ArrayList<Integer> vstack;

  /*-----------------------------------------------------------*/
  /*--- General Methods ---------------------------------------*/
  /*-----------------------------------------------------------*/

  /** Transfer an element from the real to the virtual stack.  This assumes 
   *  that the virtual stack is currently empty.  
   */
  private void getFromReal()
    {
      Symbol stack_sym;

      /* don't transfer if the real stack is empty */
      if (real_top == 0) return;

      /* get a copy of the first Symbol we have not transfered */
      stack_sym = (Symbol)real_stack.get(--real_top);

      /* put the state number from the Symbol onto the virtual stack */
      vstack.add(stack_sym.parse_state);
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Indicate whether the stack is empty. */
  public boolean empty()
    {
      /* if vstack is empty then we were unable to transfer onto it and 
	 the whole thing is empty. */
      return vstack.isEmpty();
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/
      
  /** Return value on the top of the stack (without popping it). */
  public int top() throws java.lang.Exception
    {
      if (vstack.isEmpty())
	throw new Exception(
		  "Internal parser error: top() called on empty virtual stack");

      return vstack.get(vstack.size()-1).intValue();
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Pop the stack. */
  public void pop()
    {
      assert !vstack.isEmpty() :
		  "Internal parser error: pop from empty virtual stack";

      /* pop it */
      vstack.remove(vstack.size()-1);

      /* if we are now empty transfer an element (if there is one) */
      if (vstack.isEmpty())
        getFromReal();
    }
  
  /** Pop several elements from the stack */
  public void pop(int num_elems)
    {
      int vsize = vstack.size();
      if (vsize > num_elems) 
	{
	  while (num_elems-- > 0)
	    vstack.remove(--vsize);
	}
      else 
	{
	  vstack.clear();
	  real_top -= (num_elems - vsize);
	  getFromReal();
	}
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Push a state number onto the stack. */
  public void push(int state_num)
    {
      vstack.add(state_num);
    }

  /*-----------------------------------------------------------*/

}
