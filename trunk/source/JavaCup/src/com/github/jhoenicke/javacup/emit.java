package com.github.jhoenicke.javacup;

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Date;

/** 
 * This class handles emitting generated code for the resulting parser.
 * The various parse tables must be constructed, etc. before calling any 
 * routines in this class.<p>  
 *
 * Three classes are produced by this code:
 *   <dl>
 *   <dt> symbol constant class
 *   <dd>   this contains constant declarations for each terminal (and 
 *          optionally each non-terminal).
 *   <dt> action class
 *   <dd>   this non-public class contains code to invoke all the user actions 
 *          that were embedded in the parser specification.
 *   <dt> parser class
 *   <dd>   the specialized parser class consisting primarily of some user 
 *          supplied general and initialization code, and the parse tables.
 *   </dl><p>
 *
 *  Three parse tables are created as part of the parser class:
 *    <dl>
 *    <dt> production table
 *    <dd>   lists the LHS non terminal number, and the length of the RHS of 
 *           each production.
 *    <dt> action table
 *    <dd>   for each state of the parse machine, gives the action to be taken
 *           (shift, reduce, or error) under each lookahead symbol.<br>
 *    <dt> reduce-goto table
 *    <dd>   when a reduce on a given production is taken, the parse stack is 
 *           popped back a number of elements corresponding to the RHS of the 
 *           production.  This reveals a prior state, which we transition out 
 *           of under the LHS non terminal symbol for the production (as if we
 *           had seen the LHS symbol rather than all the symbols matching the 
 *           RHS).  This table is indexed by non terminal numbers and indicates 
 *           how to make these transitions. 
 *    </dl><p>
 * 
 * In addition to the method interface, this class maintains a series of 
 * public global variables and flags indicating how misc. parts of the code 
 * and other output is to be produced, and counting things such as number of 
 * conflicts detected (see the source code and public variables below for
 * more details).<p> 
 *
 * This class is "static" (contains only data and methods).<p> 
 *
 * @see com.github.jhoenicke.javacup.main
 * @version last update: 11/25/95
 * @author Scott Hudson
 */

/* Major externally callable routines here include:
     symbols               - emit the symbol constant class 
     parser                - emit the parser class

   In addition the following major internal routines are provided:
     emit_package          - emit a package declaration
     emit_action_code      - emit the class containing the user's actions 
     emit_production_table - emit declaration and init for the production table
     do_action_table       - emit declaration and init for the action table
     do_reduce_table       - emit declaration and init for the reduce-goto table

   Finally, this class uses a number of public instance variables to communicate
   optional parameters and flags used to control how code is generated,
   as well as to report counts of various things (such as number of conflicts
   detected).  These include:

   prefix                  - a prefix string used to prefix names that would 
			     otherwise "pollute" someone else's name space.
   package_name            - name of the package emitted code is placed in 
			     (or null for an unnamed package.
   symbol_const_class_name - name of the class containing symbol constants.
   parser_class_name       - name of the class for the resulting parser.
   action_code             - user supplied declarations and other code to be 
			     placed in action class.
   parser_code             - user supplied declarations and other code to be 
			     placed in parser class.
   init_code               - user supplied code to be executed as the parser 
			     is being initialized.
   scan_code               - user supplied code to get the next Symbol.
   start_production        - the start production for the grammar.
   import_list             - list of imports for use with action class.
   num_conflicts           - number of conflicts detected. 
   nowarn                  - true if we are not to issue warning messages.
   not_reduced             - count of number of productions that never reduce.
   unused_term             - count of unused terminal symbols.
   unused_non_term         - count of unused non terminal symbols.
   *_time                  - a series of symbols indicating how long various
			     sub-parts of code generation took (used to produce
			     optional time reports in main).
*/

public class emit {

  /*-----------------------------------------------------------*/
  /*--- Variables ---------------------------------------------*/
  /*-----------------------------------------------------------*/
  
  /** The package name of javacup's runtime. */
  public final static String RUNTIME_PACKAGE = "com.github.jhoenicke.javacup.runtime";

  /** The prefix placed on names that pollute someone else's name space. */
  public final static String prefix = "CUP$";

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Package that the resulting code goes into (null is used for unnamed). */
  public String package_name = null;

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Name of the generated class for symbol constants. */
  public String symbol_const_class_name = "sym";

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Name of the generated parser class. */
  public String parser_class_name = "parser";

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

 /** TUM changes; proposed by Henning Niss 20050628: Type arguments for class declaration */
  public String class_type_argument = null;

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** User declarations for direct inclusion in user action class. */
  public String action_code = null;

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** User declarations for direct inclusion in parser class. */
  public String parser_code = null;

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** User code for user_init() which is called during parser initialization. */
  public String init_code = null;

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** User code for scan() which is called to get the next Symbol. */
  public String scan_code = null;

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** List of imports (Strings containing class names) to go with actions. */
  public ArrayList<String> import_list = new ArrayList<String>();

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Do we skip warnings? */
  public boolean nowarn = false;

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Count of the number on non-reduced productions found. */
  public int not_reduced = 0;

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Count of unused terminals. */
  public int unused_term = 0;

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Count of unused non terminals. */
  public int unused_non_term = 0;

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /* Timing values used to produce timing report in main.*/

  /** Time to produce symbol constant class. */
  public long symbols_time          = 0;

  /** Time to produce parser class. */
  public long parser_time           = 0;

  /** Time to produce action code class. */
  public long action_code_time      = 0;

  /** Time to produce the production table. */
  public long production_table_time = 0;

  /** Time to produce the action table. */
  public long action_table_time     = 0;

  /** Time to produce the reduce-goto table. */
  public long goto_table_time       = 0;

  /*-----------------------------------------------------------*/
  /*--- General Methods ---------------------------------------*/
  /*-----------------------------------------------------------*/

  /** Build a string with the standard prefix. 
   * @param str string to prefix.
   */
  protected final static String pre(String str) {
    return prefix + str;
  }

   /**
    * TUM changes; proposed by Henning Niss 20050628 
    * Build a string with the specified type arguments,
    * if present, otherwise an empty string.
    */
   protected String typeArgument() {
     return class_type_argument == null ? "" : "<" + class_type_argument + ">";
   }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Emit a package spec if the user wants one. 
   * @param out stream to produce output on.
   */
  protected void emit_package(PrintWriter out)
    {
      /* generate a package spec if we have a name for one */
      if (package_name != null) {
	out.println("package " + package_name + ";"); out.println();
      }
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/
  
  public String stackelem(int index, boolean is_java15)
    {
      String access = pre("stack") + ".get(" + pre("size") + " - " + index + ")";
      return is_java15 ? access : "((" + RUNTIME_PACKAGE + ".Symbol) "+access+")";
    }

  /** Emit code for the symbol constant class, optionally including non terms,
   *  if they have been requested.  
   * @param out            stream to produce output on.
   * @param emit_non_terms do we emit constants for non terminals?
   * @param sym_interface  should we emit an interface, rather than a class?
   */
  public void symbols(PrintWriter out, Grammar grammar, 
			     boolean emit_non_terms, boolean sym_interface)
    {
      String class_or_interface = (sym_interface)?"interface":"class";

      long start_time = System.currentTimeMillis();

      /* top of file */
      out.println();
      out.println("//----------------------------------------------------"); 
      out.println("// The following code was generated by " + 
							   version.title_str);
      out.println("// " + new Date());
      out.println("//----------------------------------------------------"); 
      out.println();
      emit_package(out);

      /* class header */
      out.println("/** CUP generated " + class_or_interface + 
		  " containing symbol constants. */");
      out.println("public " + class_or_interface + " " + 
		  symbol_const_class_name + " {");

      out.println("  /* terminals */");

      /* walk over the terminals */              /* later might sort these */
      for (terminal term : grammar.terminals())
	{

	  /* output a constant decl for the terminal */
	  out.println("  public static final int " + term.name() + " = " + 
		      term.index() + ";");
	}

      /* do the non terminals if they want them (parser doesn't need them) */
      if (emit_non_terms)
	{
          out.println();
          out.println("  /* non terminals */");

          /* walk over the non terminals */       /* later might sort these */
          for (non_terminal nt : grammar.non_terminals())
	    {
          // ****
          // TUM Comment: here we could add a typesafe enumeration
          // ****

	      /* output a constant decl for the terminal */
	      out.println("  static final int " + nt.name() + " = " + 
		          nt.index() + ";");
	    }
	}

      /* end of class */
      out.println("}");
      out.println();

      symbols_time = System.currentTimeMillis() - start_time;
    }
  
  private void emit_action(PrintWriter out, Grammar grammar, production prod,
      boolean lr_values, boolean old_lr_values, boolean is_java15)
    {
      boolean is_star_action = 
	prod.action() != null && prod.action().code_string().startsWith("CUP$STAR");
      String result = "";
      if (prod.lhs().stack_type() != null && !is_star_action)
	{
	  int lastResult = prod.getIndexOfIntermediateResult();
	  String init_result = "";
	  if (lastResult!=-1)
	    {
	      init_result =  " = (" + prod.lhs().stack_type() + ") " +
	      stackelem(prod.rhs_stackdepth() - lastResult, is_java15)+".value";
	    }
	  else if (prod instanceof action_production)
	    {
	      init_result = " = null";
	    }
	  /* create the result symbol */
	  /* make the variable RESULT which will point to the new Symbol 
	   * (see below) and be changed by action code
	   * 6/13/96 frankf */
	  out.println("              " +  prod.lhs().stack_type() +
	      " RESULT"+init_result+";");

	  result = ", RESULT";
	}

      production baseprod;
      if (prod instanceof action_production)
	baseprod = ((action_production)prod).base_production();
      else
	baseprod = prod;
      String leftsym = null, rightsym = null;
      /* Add code to propagate RESULT assignments that occur in
       * action code embedded in a production (ie, non-rightmost
       * action code). 24-Mar-1998 CSA
       */
      for (int i=prod.rhs_stackdepth()-1; i>=0; i--) 
	{
	  symbol_part symbol = baseprod.rhs(i);
	  String label = symbol.label;
	  String symtype = symbol.the_symbol.stack_type(); 
	  boolean is_wildcard = !is_star_action && symtype != null
	  	&& (symbol.the_symbol.name().endsWith("*")
		    || symbol.the_symbol.name().endsWith("+"));

	  if (label != null)
	    {
	      if (i == 0)
		leftsym = label+"$";
	      if (i == prod.rhs_stackdepth()-1)
		rightsym = label+"$";

	      out.println("              " + RUNTIME_PACKAGE + ".Symbol " + 
		  label + "$ = " +
		  stackelem(prod.rhs_stackdepth() - i, is_java15) + ";");

	      /* Put in the left/right value labels */
	      if (old_lr_values)
		{
		  out.println("              int "+label+"left = "+
		      label + "$.left;");
		  out.println("              int "+label+"right = "+
		      label + "$.right;");
		}
	      if (symtype != null)
		{
		  if (is_wildcard)
		    {
		      String basetype = symtype.substring(0, symtype.length()-2);
		      int arraySuffix = basetype.length();
		      while (basetype.charAt(arraySuffix-2) == '[')
			arraySuffix -= 2;
		      String listtype = "java.util.ArrayList";
		      String cast = "";
		      if (is_java15)
			listtype += "<" + basetype + ">";
		      else
			cast = "(" + symtype + ") ";
		      String symbollist = pre("list$" + label);
		      out.println("              " + listtype + " " + symbollist +
			  " = (" + listtype + ") " + label + "$.value;");
		      out.println("              " + symtype + " " + label + 
			  " = " + cast + symbollist + ".toArray(" +
			  "new " + basetype.substring(0, arraySuffix) + 
			  "[" + symbollist + ".size()]" + 
			  basetype.substring(arraySuffix) + ");");
		    }
		  else
		    {
		      out.println("              " + symtype +
			  " " + label + " = (" + symtype + ") " +
			  label + "$.value;");
		    }
		}
	    }
	}

      /* if there is an action string, emit it */
      if (prod.action() != null)
	{
	  if (prod.action().code_string().startsWith("CUP$STAR"))
	    {
	      assert(prod.lhs().stack_type() != null);
	      String symtype = prod.lhs().stack_type();
	      String basetype = symtype.substring(0, symtype.length()-2);
	      String listtype = "java.util.ArrayList";
	      if (is_java15)
		listtype += "<" + basetype + ">";

	      switch (prod.action().code_string().charAt(8))
	      	{
	      	  case '0':
	      	    result = ", new "+listtype+"()";
	      	    break;
	      	  case '1':
	      	    leftsym = rightsym = pre("0");
	      	    out.println("              " + RUNTIME_PACKAGE + ".Symbol " +
	      		rightsym + " = " +
	      		stackelem(prod.rhs_stackdepth(), is_java15) + ";");
	      	    out.println("              " + listtype +  
	      		" RESULT = new "+listtype+"();");
	      	    out.println("              " +   
	      		"RESULT.add((" + basetype + ") " + rightsym +".value);");
	      	    result = ", RESULT";
	      	    break;
	      	  case '2': 
	      	    leftsym = pre("0");
	      	    rightsym = pre("1");
	      	    out.println("              " + RUNTIME_PACKAGE + ".Symbol " +
	      			rightsym + " = " +
	      			stackelem(prod.rhs_stackdepth() - 1, is_java15) + ";");
	      	    out.println("              " + RUNTIME_PACKAGE + ".Symbol " +
			      	leftsym + " = " +
			      	stackelem(prod.rhs_stackdepth() - 0, is_java15) + ";");
	      	    out.println("              " + listtype +  
	      		" RESULT = ("+listtype+") " + leftsym + ".value;");
	      	    out.println("              " +   
	      		"RESULT.add((" + basetype + ") " + rightsym +".value);");
	      	    result = ", RESULT";
	      	    break;
	      	}
	    }
	  else 
	    {
	      out.println(prod.action().code_string());
	    }
	}

      /* here we have the left and right values being propagated.  
		must make this a command line option.
	     frankf 6/18/96 */

      /* Create the code that assigns the left and right values of
        the new Symbol that the production is reducing to */
      String leftright = "";
      if (lr_values)
	{
	  if (prod.rhs_length() <= 1 && rightsym == null)
	    {
	      leftsym = rightsym = pre("sym");
	      out.println("              " + RUNTIME_PACKAGE + ".Symbol " + rightsym + " = " +
		  stackelem(1, is_java15) + ";");
	    }
	  else
	    {
	      if (rightsym == null)
		rightsym = stackelem(1, is_java15);
	      if (leftsym == null)
		leftsym = stackelem(prod.rhs_stackdepth(), is_java15);
	    }
	  leftright = ", " + leftsym + ", " + rightsym;
	}
	  /* code to return lhs symbol */
	  out.println("              return parser.getSymbolFactory().newSymbol(" + 
	      "\"" + prod.lhs().name() +  "\", " +
	      prod.lhs().index() + leftright + result + ");");
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Emit code for the non-public class holding the actual action code. 
   * @param out        stream to produce output on.
   * @param start_prod the start production of the grammar.
   */
  private void emit_action_code(PrintWriter out, Grammar grammar, String action_class, 
      boolean lr_values, boolean old_lr_values, boolean is_java15)
    {
      long start_time = System.currentTimeMillis();

      /* Stack generic parameter and optional casts depending on Java Version */
      String genericArg = is_java15 ? "<" + RUNTIME_PACKAGE + ".Symbol>" : "           ";

      /* class header */
      out.println();
      out.println(
       "/** Cup generated class to encapsulate user supplied action code.*/"
      );  
      /* TUM changes; proposed by Henning Niss 20050628: added type argument */
      out.println((is_java15 ? "static ": "") + "class " +  action_class + " {");
      /* user supplied code */
      if (action_code != null)
	{
	  out.println();
          out.println(action_code);
	}

      /* field for parser object */
      /* TUM changes; proposed by Henning Niss 20050628: added typeArgument */
      out.println("  private final "+parser_class_name + typeArgument() + " parser;");

      /* constructor */
      out.println();
      out.println("  /** Constructor */");
      /* TUM changes; proposed by Henning Niss 20050628: added typeArgument */
      out.println("  " + action_class + "("+parser_class_name+typeArgument()+" parser) {");
      out.println("    this.parser = parser;");
      out.println("  }");

      /* action method head */
      out.println();
      out.println("  /** Method with the actual generated action code. */");
      if (is_java15)
	out.println("  @SuppressWarnings({ \"unused\", \"unchecked\" })");
      out.println("  public final " + RUNTIME_PACKAGE + ".Symbol " + 
		     pre("do_action") + "(");
      out.println("    int                        " + pre("act_num,"));
      out.println("    java.util.ArrayList"+genericArg+" " + pre("stack)"));
      out.println("    throws java.lang.Exception");
      out.println("    {");

      out.println("      /* Stack size for peeking into the stack */");
      out.println("      int " + pre("size") + " = "+pre("stack")+".size();");
      out.println();

      /* switch top */
      out.println("      /* select the action based on the action number */");
      out.println("      switch (" + pre("act_num") + ")");
      out.println("        {");

      /* emit action code for each production as a separate case */
      for (production prod : grammar.actions())
	{
	  /* case label */
	  for (production p2 : prod.lhs().productions())
	    {
	      if (p2.action_index() == prod.action_index())
		out.println("          // " + p2.toString());
	    }
          out.println("          case " + prod.action_index() + ":");
	  /* give them their own block to work in */
	  out.println("            {");
	  
	  emit_action(out, grammar, prod, lr_values, old_lr_values, is_java15);
	  
	  /* end of their block */
	  out.println("            }");
	  out.println();
	}

      /* end of switch */
      out.println("          /* . . . . . .*/");
      out.println("          default:");
      out.println("            throw new InternalError(");
      out.println("               \"Invalid action number found in " +
				  "internal parse table\");");
      out.println();
      out.println("        }");

      /* end of method */
      out.println("    }");

      /* end of class */
      out.println("}");
      out.println();

      action_code_time = System.currentTimeMillis() - start_time;
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Emit the production table. 
   * @param out stream to produce output on.
   */
  private String do_production_table(Grammar grammar)
    {
      long start_time = System.currentTimeMillis();

      short[] prod_table = new short[2*grammar.num_actions()];
      for (production prod : grammar.actions())
	{
	  prod_table[2*prod.action_index()+0] = (short) prod.lhs().index();
	  prod_table[2*prod.action_index()+1] = (short) prod.rhs_length();
	}
      String result = do_array_as_string(prod_table);
      production_table_time = System.currentTimeMillis() - start_time;
      return result;
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Emit the action table. 
   * @param out             stream to produce output on.
   * @param act_tab         the internal representation of the action table.
   * @param compact_reduces do we use the most frequent reduce as default?
   */
  private String do_action_table(
    Grammar            grammar)
    {
      long start_time = System.currentTimeMillis();
      parse_action_table act_tab = grammar.action_table();
      int[] base_tab = new int[act_tab.table.length];
      short[] action_tab = act_tab.compress(base_tab);
      String result = do_array_as_string(base_tab) + do_array_as_string(action_tab);
      action_table_time = System.currentTimeMillis() - start_time;
      return result;
    }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Create the compressed reduce-goto table. 
   * @param red_tab the internal representation of the reduce-goto table.
   */
  private String do_reduce_table(Grammar grammar)
    {
      parse_reduce_table red_tab = grammar.reduce_table();
      long start_time = System.currentTimeMillis();
      String result = do_array_as_string(red_tab.compress());
      goto_table_time = System.currentTimeMillis() - start_time;
      return result;
    }

  /** create a string encoding a given short[] array.*/
  private String do_array_as_string(short[] sharr) 
    {
      StringBuilder sb = new StringBuilder();
      if (sharr.length >= 0x8000)
	sb.append((char) (0x8000+(sharr.length>>16)));
      sb.append((char)(sharr.length & 0xffff));
      for (int i = 0; i < sharr.length; i++)
	sb.append((char) sharr[i]);
      return sb.toString();
    }
  
  /** create a string encoding a given short[] array.*/
  private String do_array_as_string(int[] intarr)
    {
      StringBuilder sb = new StringBuilder();
      if (intarr.length >= 0x8000)
	sb.append((char) (0x8000+(intarr.length>>16)));
      sb.append((char)(intarr.length & 0xffff));
      for (int i = 0; i < intarr.length; i++)
	{
	  assert(intarr[i] >= 0);
	  if (intarr[i] >= 0x8000)
	    sb.append((char) (0x8000+(intarr[i]>>16)));
	  sb.append((char) (intarr[i]&0xffff));
	}
      return sb.toString();
    }

  /** print a string in java source code */
  private void output_string(PrintWriter out, String str) {
    int utf8len = 0;
    for (int i = 0; i < str.length(); i += 11)
      {
	StringBuilder encoded = new StringBuilder();
	encoded.append("    \"");
	for (int j = 0; j < 11 && i+j < str.length(); j++)
	  {
	    char c = str.charAt(i+j);
	    encoded.append('\\');
	    if (c < 256) 
	      {
		String oct = "000"+Integer.toOctalString(c);
		oct = oct.substring(oct.length()-3);
		encoded.append(oct);
	      }
	    else
	      {
		String hex = "0000"+Integer.toHexString(c);
		hex = hex.substring(hex.length()-4);
		encoded.append('u').append(hex);
	      }
	    utf8len++;
	    if (c >= 128 || c == 0)
	      {
		utf8len++;
		if (c >= 2048)
		  utf8len++;
	      }
	  }
	encoded.append("\"");
	if (i+11 < str.length())
	  {
	    if (utf8len > 65000)
	      {
		encoded.append(",");
		utf8len = 0;
	      }
	    else
	      encoded.append(" +");
	  }
	out.println(encoded.toString());
      }
  }

  /*. . . . . . . . . . . . . . . . . . . . . . . . . . . . . .*/

  /** Emit the parser subclass with embedded tables. 
   * @param out             stream to produce output on.
   * @param action_table    internal representation of the action table.
   * @param reduce_table    internal representation of the reduce-goto table.
   * @param start_st        start state of the parse machine.
   * @param start_prod      start production of the grammar.
   * @param compact_reduces do we use most frequent reduce as default?
   * @param suppress_scanner should scanner be suppressed for compatibility?
   */
  public void parser(
    PrintWriter        out, 
    Grammar            grammar,
    boolean            suppress_scanner,
    boolean            lr_values,
    boolean            old_lr_values,
    boolean            is_java15)
    {
      long start_time = System.currentTimeMillis();
      
      String action_class = is_java15 ? "Action$" : pre(parser_class_name+"$action");

      /* top of file */
      out.println();
      out.println("//----------------------------------------------------"); 
      out.println("// The following code was generated by " + 
							version.title_str);
      out.println("// " + new Date());
      out.println("//----------------------------------------------------"); 
      out.println();
      emit_package(out);

      /* user supplied imports */
      for (String imp : import_list)
	out.println("import " + imp + ";");

      /* class header */
      out.println();
      out.println("/** "+version.title_str+" generated parser.");
      out.println("  * @version " + new Date());
      out.println("  */");
      /* TUM changes; proposed by Henning Niss 20050628: added typeArgument */
      out.println("public class " + parser_class_name + typeArgument() +
		  " extends " + RUNTIME_PACKAGE + ".LRParser {");

      /* constructors [CSA/davidm, 24-jul-99] */
      out.println();
      out.println("  /** Default constructor. */");
      out.println("  public " + parser_class_name + "() {super();}");
      if (!suppress_scanner) {
	  out.println();
	  out.println("  /** Constructor which sets the default scanner. */");
	  out.println("  public " + parser_class_name + 
		      "(" + RUNTIME_PACKAGE + ".Scanner s) {super(s);}");
          // TUM 20060327 added SymbolFactory aware constructor
	  out.println();
	  out.println("  /** Constructor which sets the default scanner. */");
	  out.println("  public " + parser_class_name + 
		      "(" + RUNTIME_PACKAGE + ".Scanner s, " + RUNTIME_PACKAGE + ".SymbolFactory sf) {super(s,sf);}");
      }

      /* emit the various tables */
      String tables = do_production_table(grammar) + 
      	do_action_table(grammar) +
      	do_reduce_table(grammar);

      /* instance of the action encapsulation class */
      out.println("  /** Return action table */");
      out.println("  protected String[] action_table() { ");
      out.println("    return new String[] {");
      output_string(out, tables);
      out.println("    };");
      out.println("  }");
      out.println();

      /* instance of the action encapsulation class */
      out.println("  /** Instance of action encapsulation class. */");
      out.println("  protected " + action_class + " action_obj;");
      out.println();

      /* action object initializer */
      out.println("  /** Action encapsulation object initializer. */");
      out.println("  protected void init_actions()");
      out.println("    {");
      out.println("      action_obj = new " + action_class + "(this);");
      out.println("    }");
      out.println();

      /* access to action code */
      out.println("  /** Invoke a user supplied parse action. */");
      out.println("  public " + RUNTIME_PACKAGE + ".Symbol do_action(");
      out.println("    int                        act_num,");
      if (is_java15)
	out.println("    java.util.ArrayList<" + RUNTIME_PACKAGE + ".Symbol> stack)");
      else
	out.println("    java.util.ArrayList        stack)");
      out.println("    throws java.lang.Exception");
      out.println("  {");
      out.println("    /* call code in generated class */");
      out.println("    return action_obj." + pre("do_action(") +
                  "act_num, stack);");
      out.println("  }");
      out.println("");

      /* user supplied code for user_init() */
      if (init_code != null)
	{
          out.println();
	  out.println("  /** User initialization code. */");
	  out.println("  public void user_init() throws java.lang.Exception");
	  out.println("    {");
	  out.println(init_code);
	  out.println("    }");
	}

      /* user supplied code for scan */
      if (scan_code != null)
	{
          out.println();
	  out.println("  /** Scan to get the next Symbol. */");
	  out.println("  public " + RUNTIME_PACKAGE + ".Symbol scan()");
	  out.println("    throws java.lang.Exception");
	  out.println("    {");
	  out.println(scan_code);
	  out.println("    }");
	}

      /* user supplied code */
      if (parser_code != null)
	{
	  out.println();
          out.println(parser_code);
	}

      if (is_java15)
	{
	  /* put out the action code class as inner class */
	  emit_action_code(out, grammar, action_class, lr_values, old_lr_values, is_java15);

	  /* end of class */
	  out.println("}");
	} 
      else
	{
	  /* end of class */
	  out.println("}");

	  /* put out the action code class */
	  emit_action_code(out, grammar, action_class, lr_values, old_lr_values, is_java15);
	}

      parser_time = System.currentTimeMillis() - start_time;
    }

  public void usage(String message)
    {
    }
  

}
