package com.github.jhoenicke.javacup;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.InputStream;
import java.io.PrintWriter;

import com.github.jhoenicke.javacup.runtime.ComplexSymbolFactory;


/**
 * This class serves as the main driver for the JavaCup system. It accepts user
 * options and coordinates overall control flow. The main flow of control
 * includes the following activities:
 * <ul>
 * <li> Parse user supplied arguments and options.
 * <li> Open output files.
 * <li> Parse the specification from standard input.
 * <li> Check for unused terminals, non-terminals, and productions.
 * <li> Build the state machine, tables, etc.
 * <li> Output the generated code.
 * <li> Close output files.
 * <li> Print a summary if requested.
 * </ul>
 * 
 * Options to the main program include:
 * <dl>
 * <dt> -package name
 * <dd> specify package generated classes go in [default none]
 * <dt> -parser name
 * <dd> specify parser class name [default "parser"]
 * <dt> -symbols name
 * <dd> specify name for symbol constant class [default "sym"]
 * <dt> -interface
 * <dd> emit symbol constant <i>interface</i>, rather than class
 * <dt> -nonterms
 * <dd> put non terminals in symbol constant class
 * <dt> -expect #
 * <dd> number of conflicts expected/allowed [default 0]
 * <dt> -compact_red
 * <dd> compact tables by defaulting to most frequent reduce
 * <dt> -nowarn
 * <dd> don't warn about useless productions, etc.
 * <dt> -nosummary
 * <dd> don't print the usual summary of parse states, etc.
 * <dt> -progress
 * <dd> print messages to indicate progress of the system
 * <dt> -time
 * <dd> print time usage summary
 * <dt> -dump_grammar
 * <dd> produce a dump of the symbols and grammar
 * <dt> -dump_states
 * <dd> produce a dump of parse state machine
 * <dt> -dump_tables
 * <dd> produce a dump of the parse tables
 * <dt> -dump
 * <dd> produce a dump of all of the above
 * <dt> -debug
 * <dd> turn on debugging messages within JavaCup
 * <dt> -nopositions
 * <dd> don't generate the positions code
 * <dt> -noscanner
 * <dd> don't refer to com.github.jhoenicke.javacup.runtime.Scanner in the parser (for compatibility
 * with old runtimes)
 * <dt> -version
 * <dd> print version information for JavaCUP and halt.
 * </dl>
 * 
 * @version last updated: 7/3/96
 * @author Frank Flannery
 */

public class Main {

  /*-------------------------*/
  /* Options set by the user */
  /*-------------------------*/
  /** User option -- do we print progress messages. */
  private boolean print_progress = false;
  /** User option -- do we produce a dump of the state machine */
  private boolean opt_dump_states = false;
  /** User option -- do we produce a dump of the parse tables */
  private boolean opt_dump_tables = false;
  /** User option -- do we produce a dump of the grammar */
  private boolean opt_dump_grammar = false;
  /** User option -- do we show timing information as a part of the summary */
  private boolean opt_show_timing = false;
  /** User option -- do we run produce extra debugging messages */
  private boolean opt_do_debug = false;
  /**
   * User option -- do we compact tables by making most common reduce the
   * default action
   */
  private boolean opt_compact_red = false;
  /** User option -- use java 1.5 syntax (generics, annotations) */
  private boolean opt_java15 = false;
  /**
   * User option -- should we include non terminal symbol numbers in the symbol
   * constant class.
   */
  private boolean include_non_terms = false;
  /** User option -- do not print a summary. */
  private boolean no_summary = false;
  /** User option -- number of conflicts to expect */
  private int expect_conflicts = 0;

  /* frankf added this 6/18/96 */
  /** User option -- should generator update left/right values? */
  private boolean opt_lr_values = true;
  /**
   * User option -- should generator generate old style access for left/right
   * values?
   */
  private boolean opt_old_lr_values = true;

  /** User option -- should symbols be put in a class or an interface? [CSA] */
  private boolean sym_interface = false;

  /**
   * User option -- should generator suppress references to
   * com.github.jhoenicke.javacup.runtime.Scanner for compatibility with old runtimes?
   */
  private boolean suppress_scanner = false;

  /*----------------------------------------------------------------------*/
  /* Timing data (not all of these time intervals are mutually exclusive) */
  /*----------------------------------------------------------------------*/
  /** Timing data -- when did we start */
  private long start_time = 0;
  /** Timing data -- when did we end preliminaries */
  private long prelim_end = 0;
  /** Timing data -- when did we end parsing */
  private long parse_end = 0;
  /** Timing data -- when did we end checking */
  private long check_end = 0;
  /** Timing data -- when did we end dumping */
  private long dump_end = 0;
  /** Timing data -- when did we end state and table building */
  private long build_end = 0;
  /** Timing data -- when did we end nullability calculation */
  private long nullability_end = 0;
  /** Timing data -- when did we end first set calculation */
  private long first_end = 0;
  /** Timing data -- when did we end state machine construction */
  private long machine_end = 0;
  /** Timing data -- when did we end table construction */
  private long table_end = 0;
  /** Timing data -- when did we end checking for non-reduced productions */
  private long reduce_check_end = 0;
  /** Timing data -- when did we finish emitting code */
  private long emit_end = 0;
  /** Timing data -- when were we completely done */
  private long final_time = 0;

  emit emit = new emit();

  /* Additional timing information is also collected in emit */

  /*-----------------------------------------------------------*/
  /*--- Constructor(s) ----------------------------------------*/
  /*-----------------------------------------------------------*/

  public Main()
    {
      start_time = System.currentTimeMillis();
    }

  public boolean run() throws Exception
    {
      boolean did_output = false;

      prelim_end = System.currentTimeMillis();

      /* parse spec into internal data structures */
      if (print_progress)
	System.err.println("Parsing specification...");
      Grammar grammar = parse_grammar_spec();
      grammar.add_wildcard_rules();

      parse_end = System.currentTimeMillis();

      /* don't proceed unless we are error free */
      if (ErrorManager.getManager().getErrorCount() == 0)
	{
	  /* check for unused bits */
	  if (print_progress)
	    System.err.println("Checking specification...");
	  check_unused(grammar);

	  check_end = System.currentTimeMillis();

	  /* build the state machine and parse tables */
	  if (print_progress)
	    System.err.println("Building parse tables...");
	  build_parser(grammar);

	  build_end = System.currentTimeMillis();

	  /* output the generated code, if # of conflicts permits */
	  if (ErrorManager.getManager().getErrorCount() != 0)
	    {
	      // conflicts! don't emit code, don't dump tables.
	      opt_dump_tables = false;
	    }
	  else
	    { // everything's okay, emit parser.
	      if (print_progress)
		System.err.println("Writing parser...");
	      open_files();
	      emit_parser(grammar);
	      did_output = true;
	      /* close input/output files */
	      if (print_progress)
		System.err.println("Closing files...");
	      close_files();
	    }
	}
      /* fix up the times to make the summary easier */
      emit_end = System.currentTimeMillis();

      /* do requested dumps */
      if (opt_dump_grammar)
	grammar.dump_grammar();
      if (opt_dump_states)
	grammar.dump_machine();
      if (opt_dump_tables)
	grammar.dump_tables();

      dump_end = System.currentTimeMillis();

      /* produce a summary if desired */
      if (!no_summary)
	emit_summary(grammar, did_output);

      return ErrorManager.getManager().getErrorCount() == 0; 
    }

  /* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . */

  /**
   * Print a "usage message" that described possible command line options, then
   * exit.
   * 
   * @param message
   *                a specific error message to preface the usage message by.
   */
  private void usage()
    {
      System.err.println();
      System.err
	  .println("Usage: "
	      + version.program_name
	      + " [options] [filename]\n"
	      + "  and expects a specification file on standard input if no filename is given.\n"
	      + "  Legal options include:\n"
	      + "    -package name  specify package generated classes go in [default none]\n"
	      + "    -destdir name  specify the destination directory, to store the generated files in\n"
	      + "    -parser name   specify parser class name [default \"parser\"]\n"
	      + "    -typearg args  specify type arguments for parser class\n"
	      + "    -symbols name  specify name for symbol constant class [default \"sym\"]\n"
	      + "    -interface     put symbols in an interface, rather than a class\n"
	      + "    -nonterms      put non terminals in symbol constant class\n"
	      + "    -expect #      number of conflicts expected/allowed [default 0]\n"
	      + "    -compact_red   compact tables by defaulting to most frequent reduce\n"
	      + "    -newpositions  don't generate old style access for left and right token\n"
	      + "    -nowarn        don't warn about useless productions, etc.\n"
	      + "    -nosummary     don't print the usual summary of parse states, etc.\n"
	      + "    -nopositions   don't propagate the left and right token position values\n"
	      + "    -noscanner     don't refer to com.github.jhoenicke.javacup.runtime.Scanner\n"
	      + "    -progress      print messages to indicate progress of the system\n"
	      + "    -time          print time usage summary\n"
	      + "    -dump_grammar  produce a human readable dump of the symbols and grammar\n"
	      + "    -dump_states   produce a dump of parse state machine\n"
	      + "    -dump_tables   produce a dump of the parse tables\n"
	      + "    -dump          produce a dump of all of the above\n"
	      + "    -version       print the version information for CUP and exit\n");
      System.exit(1);
    }

  public boolean setOption(String option)
    {
      return setOption(option, null);
    }

  public boolean setOption(String option, String arg)
    {
      /* try to get the various options */
      if (option.equals("package"))
	{
	  /* must have an arg */
	  if (arg != null)
	    {
	      /* record the name */
	      emit.package_name = arg;
	      return true;
	    } else
	    System.err.println("package must have a name argument");
	}
      else if (option.equals("destdir"))
	{
	  /* must have an arg */
	  if (arg != null)
	    {
	      /* record the name */
	      dest_dir = new File(arg);
	      return true;
	    } else
	    System.err.println("destdir must have a name argument");
	  /* record the name */
	}
      else if (option.equals("parser"))
	{
	  /* must have an arg */
	  if (arg != null)
	    {
	      /* record the name */
	      emit.parser_class_name = arg;
	      return true;
	    } else
	    System.err.println("parser must have a name argument");
	}
      /* TUM changes; suggested by Henning Niss 20050628 */
      else if (option.equals("typearg"))
	{
	  if (arg == null)
	    System.err.println("symbols must have a name argument");
	  else
	    {
	      /* record the typearg */
	      opt_java15 = true;
	      emit.class_type_argument = option;
	      return true;
	    }
	}
      else if (option.equals("symbols"))
	{
	  /* must have an arg */
	  if (arg != null)
	    {
	      /* record the name */
	      emit.symbol_const_class_name = arg;
	      return true;
	    } else
	    System.err.println("symbols must have a name argument");
	}
      else if (option.equals("nonterms"))
	{
	  include_non_terms = true;
	  return true;
	}
      else if (option.equals("expect"))
	{
	  /* must have an arg */
	  if (arg == null)
	    System.err.println("expect must have a number argument");
	  else
	    {
	      /* record the number */
	      try
		{
		  expect_conflicts = Integer.parseInt(arg);
		  return true;
		} catch (NumberFormatException e)
		{
		  System.err
		      .println("expect must be followed by a decimal integer");
		}
	    }
	}
      else if (option.equals("java15"))
	{
	  opt_java15 = true;
	  return true;
	}
      else if (option.equals("compact_red"))
	{
	  opt_compact_red = true;
	  return true;
	}
      else if (option.equals("nosummary"))
	{
	  no_summary = true;
	  return true;
	}
      else if (option.equals("nowarn"))
	{
	  emit.nowarn = true;
	  return true;
	}
      else if (option.equals("dump_states"))
	{
	  opt_dump_states = true;
	  return true;
	}
      else if (option.equals("dump_tables"))
	{
	  opt_dump_tables = true;
	  return true;
	}
      else if (option.equals("progress"))
	{
	  print_progress = true;
	  return true;
	}
      else if (option.equals("dump_grammar"))
	{
	  opt_dump_grammar = true;
	  return true;
	}
      else if (option.equals("dump"))
	{
	  opt_dump_states = opt_dump_tables = opt_dump_grammar = true;
	  return true;
	}
      else if (option.equals("time"))
	{
	  opt_show_timing = true;
	  return true;
	}
      else if (option.equals("debug"))
	{
	  opt_do_debug = true;
	  return true;
	}
      /* frankf 6/18/96 */
      else if (option.equals("nopositions"))
	{
	  opt_lr_values = false;
	  opt_old_lr_values = false;
	  return true;
	}
      /* joho 2008-11-10 */
      else if (option.equals("newpositions"))
	{
	  opt_old_lr_values = false;
	  return true;
	}
      /* CSA 12/21/97 */
      else if (option.equals("interface"))
	{
	  sym_interface = true;
	  return true;
	}
      /* CSA 23-Jul-1999 */
      else if (option.equals("noscanner"))
	{
	  suppress_scanner = true;
	  return true;
	}
      /* CSA 23-Jul-1999 */
      else
	{
	  System.err.println("Unrecognized option \"" + option + "\"");
	}

      return false;
      /*-----------------------------------------------------------*/
    }

  /* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . */

  /**
   * Parse command line options and arguments to set various user-option flags
   * and variables.
   * 
   * @param argv
   *                the command line arguments to be parsed.
   */
  private void parse_args(String argv[])
    {
      int len = argv.length;
      int i;
      
      /* parse the options */
      for (i=0; i<len; i++)
	{
	  String option = argv[i];
	  /* try to get the various options */
	  if (option.equals("-package")
	      || option.equals("-destdir")
	      || option.equals("-parser")
	      || option.equals("-typearg")
	      || option.equals("-symbols")
	      || option.equals("-expect"))
	    {
	      /* must have an arg */
	      if (++i >= len || argv[i].startsWith("-") || 
				argv[i].endsWith(".cup"))
		System.err.println(option+" must have an argument");
	      else if (!setOption(option.substring(1), argv[i]))
		usage();
	    }
	  else if (argv[i].equals("-version"))
	    {
	      System.out.println(version.title_str);
	      System.exit(1);
	    }
	  else if (option.startsWith("-"))
	    {
	      if (!setOption(option.substring(1)))
		usage();
	    }
	  /* CSA 24-Jul-1999; suggestion by Jean Vaucher */
	  else if (!argv[i].startsWith("-") && i==len-1)
	    {
	      /* use input from file. */
	      try {
		  input_file = new FileInputStream(argv[i]);
	      } catch (FileNotFoundException e) {
		  System.err.println("Unable to open \"" + argv[i] +"\" for input");
		  usage();
	      }
	    }
	  else
	    {
	      System.err.println("Unrecognized option \"" + argv[i] + "\"");
	      usage();
	    }
	}
    }

  /* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . */

  /*-------*/
  /* Files */
  /*-------*/

  /** Input file. This defaults to System.in. */
  private InputStream input_file = System.in;

  /** Output file for the parser class. */
  private PrintWriter parser_class_file;

  /** Output file for the symbol constant class. */
  private PrintWriter symbol_class_file;

  /** Output directory. */
  private File dest_dir = null;

  /* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . */

  /** Open various files used by the system. */
  private void open_files()
    {
      File fil;
      String out_name;

      /* open each of the output files */

      /* parser class */
      out_name = emit.parser_class_name + ".java";
      fil = new File(dest_dir, out_name);
      try
	{
	  parser_class_file = new PrintWriter(new BufferedOutputStream(
	      new FileOutputStream(fil), 4096));
	} catch (Exception e)
	{
	  System.err.println("Can't open \"" + out_name + "\" for output");
	  System.exit(3);
	}

      /* symbol constants class */
      out_name = emit.symbol_const_class_name + ".java";
      fil = new File(dest_dir, out_name);
      try
	{
	  symbol_class_file = new PrintWriter(new BufferedOutputStream(
	      new FileOutputStream(fil), 4096));
	} catch (Exception e)
	{
	  System.err.println("Can't open \"" + out_name + "\" for output");
	  System.exit(4);
	}
    }

  /* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . */

  /** Close various files used by the system. */
  private void close_files() throws java.io.IOException
    {
      if (parser_class_file != null)
	parser_class_file.close();
      if (symbol_class_file != null)
	symbol_class_file.close();
    }

  /* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . */

  /**
   * Parse the grammar specification from standard input. This produces sets of
   * terminal, non-terminals, and productions which can be accessed via
   * variables of the respective classes, as well as the setting of various
   * variables (mostly in the emit class) for small user supplied items such as
   * the code to scan with.
   */
  private Grammar parse_grammar_spec()
    {
      parser parser_obj;

      /* create a parser and parse with it */
      ComplexSymbolFactory csf = new ComplexSymbolFactory();
      parser_obj = new parser(new Lexer(input_file, csf), csf);
      parser_obj.main = this;
      parser_obj.emit = emit;
      try
	{
	  Grammar grammar;
	  if (opt_do_debug)
	    grammar = (Grammar) parser_obj.debug_parse().value;
	  else
	    grammar = (Grammar) parser_obj.parse().value;
	  if (input_file != System.in)
	    input_file.close();
	  return grammar;
	}
      catch (Exception e)
	{
	  /* The parser should never throw an exception */
	  AssertionError error = new AssertionError("Exception in parser");
	  error.initCause(e); 
	  throw error;
	}
    }

  /* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . */

  /**
   * Check for unused symbols. Unreduced productions get checked when tables are
   * created.
   */
  private void check_unused(Grammar grammar)
    {
      /* check for unused terminals */
      for (terminal term : grammar.terminals())
	{
	  /* don't issue a message for EOF */
	  if (term == terminal.EOF)
	    continue;

	  /* or error */
	  if (term == terminal.error)
	    continue;

	  /* is this one unused */
	  if (term.use_count() == 0)
	    {
	      /* count it and warn if we are doing warnings */
	      emit.unused_term++;
	      if (!emit.nowarn)
		{
		  ErrorManager.getManager().emit_warning(
		      "Terminal \"" + term.name()
			  + "\" was declared but never used");
		}
	    }
	}

      /* check for unused non terminals */
      for (non_terminal nt : grammar.non_terminals())
	{
	  /* is this one unused */
	  if (nt.use_count() == 0 || nt.productions().size() == 0)
	    {
	      /* count and warn if we are doing warnings */
	      emit.unused_non_term++;
	      if (!emit.nowarn)
		{
		  String reason;
		  if (nt.use_count() == 0)
		    reason = "\" was declared but never used";
		  else
		    reason = "\" has no production";
		  ErrorManager.getManager().emit_warning(
		      "Non terminal \"" + nt.name() + reason);
		}
	    }
	}

    }

  /* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . */

  /**
   * Build the (internal) parser from the previously parsed specification. This
   * includes:
   * <ul>
   * <li> Computing nullability of non-terminals.
   * <li> Computing first sets of non-terminals and productions.
   * <li> Building the viable prefix recognizer machine.
   * <li> Filling in the (internal) parse tables.
   * <li> Checking for unreduced productions.
   * </ul>
   */
  private void build_parser(Grammar grammar)
    {
      /* compute nullability of all non terminals */
      if (opt_do_debug || print_progress)
	System.err.println("  Computing non-terminal nullability...");
      grammar.compute_nullability();

      nullability_end = System.currentTimeMillis();

      /* compute first sets of all non terminals */
      if (opt_do_debug || print_progress)
	System.err.println("  Computing first sets...");
      grammar.compute_first_sets();

      first_end = System.currentTimeMillis();

      /* build the LR viable prefix recognition machine */
      if (opt_do_debug || print_progress)
	System.err.println("  Building state machine...");
      grammar.build_machine();

      machine_end = System.currentTimeMillis();

      /* build the LR parser action and reduce-goto tables */
      if (opt_do_debug || print_progress)
	System.err.println("  Filling in tables...");
      grammar.build_tables(opt_compact_red);

      table_end = System.currentTimeMillis();

      /* check and warn for non-reduced productions */
      if (opt_do_debug || print_progress)
	System.err.println("  Checking for non-reduced productions...");
      if (!emit.nowarn)
	grammar.check_tables();
      reduce_check_end = System.currentTimeMillis();

      /* if we have more conflicts than we expected issue a message and die */
      if (grammar.num_conflicts() > expect_conflicts)
	{
	  ErrorManager.getManager().emit_error(
	      "*** More conflicts encountered than expected "
		  + "-- parser generation aborted");
	  // indicate the problem.
	  // we'll die on return, after clean up.
	}
    }

  /* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . */

  /** Call the emit routines necessary to write out the generated parser. */
  private void emit_parser(Grammar grammar)
    {
      emit.symbols(symbol_class_file, grammar, include_non_terms, sym_interface);
      emit.parser(parser_class_file, grammar,
	  suppress_scanner,
	  opt_lr_values, opt_old_lr_values, opt_java15);
    }

  /* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . */

  /**
   * Helper routine to optionally return a plural or non-plural ending.
   * 
   * @param val
   *                the numerical value determining plurality.
   */
  private String plural(int val)
    {
      if (val == 1)
	return "";
      else
	return "s";
    }

  /* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . */

  /**
   * Emit a long summary message to standard error (System.err) which summarizes
   * what was found in the specification, how many states were produced, how
   * many conflicts were found, etc. A detailed timing summary is also produced
   * if it was requested by the user.
   * 
   * @param output_produced
   *                did the system get far enough to generate code.
   */
  private void emit_summary(Grammar grammar, boolean output_produced)
    {
      final_time = System.currentTimeMillis();

      System.err.println("------- " + version.title_str
	  + " Parser Generation Summary -------");

      /* error and warning count */
      System.err.println("  " + ErrorManager.getManager().getErrorCount()
	  + " error" + plural(ErrorManager.getManager().getErrorCount())
	  + " and " + ErrorManager.getManager().getWarningCount() + " warning"
	  + plural(ErrorManager.getManager().getWarningCount()));

      /* basic stats */
      System.err.print("  " + grammar.num_terminals() + " terminal"
	  + plural(grammar.num_terminals()) + ", ");
      System.err.print(grammar.num_non_terminals() + " non-terminal"
	  + plural(grammar.num_non_terminals()) + ", and ");
      System.err.println(grammar.num_productions() + " production"
	  + plural(grammar.num_productions()) + " declared, ");
      System.err.print("  producing " + grammar.lalr_states().size()
	  + " unique parse states,");
      System.err.println(" " + grammar.num_actions() + " unique action"
	  + plural(grammar.num_actions()) + ". ");

      /* unused symbols */
      System.err.println("  " + emit.unused_term + " terminal"
	  + plural(emit.unused_term) + " declared but not used.");
      System.err.println("  " + emit.unused_non_term + " non-terminal"
	  + plural(emit.unused_non_term) + " declared but not used.");

      /* productions that didn't reduce */
      System.err.println("  " + emit.not_reduced + " production"
	  + plural(emit.not_reduced) + " never reduced.");

      /* conflicts */
      System.err.println("  " + grammar.num_conflicts() + " conflict"
	  + plural(grammar.num_conflicts()) + " detected" + " ("
	  + expect_conflicts + " expected).");

      /* code location */
      if (output_produced)
	System.err.println("  Code written to \"" + emit.parser_class_name
	    + ".java\", and \"" + emit.symbol_const_class_name + ".java\".");
      else
	System.err.println("  No code produced.");

      if (opt_show_timing)
	show_times();

      System.err
	  .println("---------------------------------------------------- ("
	      + version.version_str + ")");
    }

  /* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . */

  /** Produce the optional timing summary as part of an overall summary. */
  private void show_times()
    {
      long total_time = final_time - start_time;

      System.err.println(". . . . . . . . . . . . . . . . . . . . . . . . . ");
      System.err.println("  Timing Summary");
      System.err.println("    Total time       "
	  + timestr(final_time - start_time, total_time));
      System.err.println("      Startup        "
	  + timestr(prelim_end - start_time, total_time));
      System.err.println("      Parse          "
	  + timestr(parse_end - prelim_end, total_time));
      if (check_end != 0)
	System.err.println("      Checking       "
	    + timestr(check_end - parse_end, total_time));
      if (check_end != 0 && build_end != 0)
	System.err.println("      Parser Build   "
	    + timestr(build_end - check_end, total_time));
      if (nullability_end != 0 && check_end != 0)
	System.err.println("        Nullability  "
	    + timestr(nullability_end - check_end, total_time));
      if (first_end != 0 && nullability_end != 0)
	System.err.println("        First sets   "
	    + timestr(first_end - nullability_end, total_time));
      if (machine_end != 0 && first_end != 0)
	System.err.println("        State build  "
	    + timestr(machine_end - first_end, total_time));
      if (table_end != 0 && machine_end != 0)
	System.err.println("        Table build  "
	    + timestr(table_end - machine_end, total_time));
      if (reduce_check_end != 0 && table_end != 0)
	System.err.println("        Checking     "
	    + timestr(reduce_check_end - table_end, total_time));
      if (emit_end != 0 && build_end != 0)
	System.err.println("      Code Output    "
	    + timestr(emit_end - build_end, total_time));
      if (emit.symbols_time != 0)
	System.err.println("        Symbols      "
	    + timestr(emit.symbols_time, total_time));
      if (emit.parser_time != 0)
	System.err.println("        Parser class "
	    + timestr(emit.parser_time, total_time));
      if (emit.action_code_time != 0)
	System.err.println("          Actions    "
	    + timestr(emit.action_code_time, total_time));
      if (emit.production_table_time != 0)
	System.err.println("          Prod table "
	    + timestr(emit.production_table_time, total_time));
      if (emit.action_table_time != 0)
	System.err.println("          Action tab "
	    + timestr(emit.action_table_time, total_time));
      if (emit.goto_table_time != 0)
	System.err.println("          Reduce tab "
	    + timestr(emit.goto_table_time, total_time));

      System.err.println("      Dump Output    "
	  + timestr(dump_end - emit_end, total_time));
    }

  /* . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . */

  /**
   * Helper routine to format a decimal based display of seconds and percentage
   * of total time given counts of milliseconds. Note: this is broken for use
   * with some instances of negative time (since we don't use any negative time
   * here, we let if be for now).
   * 
   * @param time_val
   *                the value being formatted (in ms).
   * @param total_time
   *                total time percentages are calculated against (in ms).
   */
  private String timestr(long time_val, long total_time)
    {
      long percent10;

      /* pull out seconds and ms */
      /* construct a pad to blank fill seconds out to 4 places */
      String sec = "   "+(time_val / 1000);
      String ms  = "00"+(time_val % 1000);

      /* calculate 10 times the percentage of total */
      percent10 = (time_val * 1000) / total_time;

      /* build and return the output string */
      return sec.substring(sec.length() - 4) + "."
          + ms.substring(ms.length() - 3) + "sec"
          + " (" + percent10 / 10 + "." + percent10 % 10 + "%)";
    }

  /*-----------------------------------------------------------*/

  /*-----------------------------------------------------------*/
  /*--- Main Program ------------------------------------------*/
  /*-----------------------------------------------------------*/

  /**
   * The main driver for the system.
   * 
   * @param argv
   *                an array of strings containing command line arguments.
   */
  public static void main(String argv[]) throws Exception
    {
      Main main = new Main();

      /* process user options and arguments */
      main.parse_args(argv);
      boolean success = main.run();

      /*
       * If there were errors during the run, exit with non-zero status
       * (makefile-friendliness). --CSA
       */
      if (!success)
	System.exit(1);
    }

}
