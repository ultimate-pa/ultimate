package local.stalin.nativez3;

import java.io.FileReader;
import java.io.InputStreamReader;
import java.io.Reader;

import org.apache.log4j.ConsoleAppender;
import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.apache.log4j.SimpleLayout;

import local.stalin.logic.Formula;
import local.stalin.nativez3.Z3ProofRule.Z3ProofRulePrinter;
import local.stalin.smt.smtlib.Benchmark;
import local.stalin.smt.smtlib.Lexer;
import local.stalin.smt.smtlib.MySymbolFactory;
import local.stalin.smt.smtlib.Parser;

public class Test {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		try {
			Logger logger = Logger.getRootLogger();
			SimpleLayout layout = new SimpleLayout();
	        logger.addAppender(new ConsoleAppender(layout));
	        // ALL | DEBUG | INFO | WARN | ERROR | FATAL | OFF:
	        logger.setLevel(Level.ALL);

	        // Parse SMTLIB input into our internal representation
			MySymbolFactory symfactory = new MySymbolFactory();
			Reader reader;
			if (args.length > 0) {
				reader = new FileReader(args[0]);
			} else {
				reader = new InputStreamReader(System.in);
			}
			Lexer lexer = new Lexer(reader);
			lexer.setSymbolFactory(symfactory);
			Parser parser = new Parser(lexer, symfactory);
			Benchmark b = (Benchmark) parser.parse().value;
	        // Use configuration which creates models and proofs
			Z3Config cfg = new Z3Config.Z3ConfigModelProof();
			/* Set another configuration: 
			 * My input formula is in array property fragment: Z3 can decide it
			 */
			cfg.setConfig("ARRAY_PROPERTY","true");
			/* Create a logical context. Theory argument is still mutable
			 * whereas modifications to the configuration will not be
			 * recognized!
			 */
			Z3Context ctx = new Z3Context(cfg,b.getTheory());
			// Allow VM to free some space since we do not need the configuration anymore
			cfg = null;
			
			// Now create a parser to parse our representation into Z3 internal representation
			Z3Parser z3parser = ctx.getParser();
			for( Formula ass : b.getFormulae() )
				z3parser.addAssumption(ass);
			int res = ctx.checkAndGetProof();
			switch( res ) {
			case Z3Context.Z3SAT:
				System.err.println("Satisfiable");
				// TODO: If Model is implemented, print it.
				break;
			case Z3Context.Z3UNKNOWN:
				System.err.println("Unknown! Last Error:");
				System.err.println(ctx.getLastFailureDescription());
				// TODO: If Model is implemented, print it.
				break;
			case Z3Context.Z3UNSAT:
				System.err.println("Unsatisfiable! Proof:");
				Z3ProofRulePrinter prp = new Z3ProofRule.Z3ProofRulePrinter(System.err);
				prp.print(ctx.getProof());
			}
		} catch (Exception e) {
			e.printStackTrace(System.err);
		}
	}

}
