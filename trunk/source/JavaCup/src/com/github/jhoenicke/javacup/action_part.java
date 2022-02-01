
package com.github.jhoenicke.javacup;

/** 
 * This class represents a part of a production which contains an
 * action.  These are eventually eliminated from productions and converted
 * to trailing actions by factoring out with a production that derives the
 * empty string (and ends with this action).
 *
 * @see com.github.jhoenicke.javacup.production
 * @version last update: 11/25/95
 * @author Scott Hudson
 */

public class action_part extends production_part {

  /*-----------------------------------------------------------*/
  /*--- Constructors ------------------------------------------*/
  /*-----------------------------------------------------------*/

  /** Simple constructor. 
   * @param code_str string containing the actual user code.
   */
  public action_part(String code_str)
    {
      _code_string = code_str;
    }

  /*-----------------------------------------------------------*/
  /*--- (Access to) Instance Variables ------------------------*/
  /*-----------------------------------------------------------*/

  /** String containing code for the action in question. */
  protected String _code_string;

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** String containing code for the action in question. */
  public String code_string() {return _code_string;}
  
  public void add_code_string(String more_action)
    {
      _code_string += more_action;
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Set the code string. */
  public void set_code_string(String new_str) {_code_string = new_str;}

  /*-----------------------------------------------------------*/
  /*--- General Methods ---------------------------------------*/
  /*-----------------------------------------------------------*/

  /** Convert to a string.  */
  public String toString()
    {
      return super.toString() + "{" + code_string() + "}";
    }

  /*-----------------------------------------------------------*/
}
