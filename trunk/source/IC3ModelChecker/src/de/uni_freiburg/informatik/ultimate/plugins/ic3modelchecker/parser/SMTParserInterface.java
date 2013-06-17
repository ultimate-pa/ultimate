package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.parser;

import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

import java_cup.runtime.Symbol;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Lexer;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.LexerSymbols;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.MySymbolFactory;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Parser;

public class SMTParserInterface {
	public static Term parse(InputStreamReader input, Script script) {
		Parser parser = new Parser();
		parser.setScript(script);
		
		Lexer lexer = new Lexer(input);
		lexer.setSymbolFactory(new MySymbolFactory());
		List<Symbol> lexerResult = parseSexpr(lexer);
//		for (Symbol symbol : lexerResult) {
//			System.out.print(symbol+" ");
//		}
//		TreeIC3.logger().debug("");

		ArrayList<Symbol> toParse = new ArrayList<Symbol>();
		toParse.add(new Symbol(LexerSymbols.GETTERM));
		toParse.addAll(lexerResult);
		parser.setAnswer(toParse);
		Symbol result = null;
		try {
			result = parser.parse();
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			throw new RuntimeException("Couldn't parse!");
		}
		
//		TreeIC3.logger().debug("Parser returned "+result.value);
		return (Term) result.value;
	}
	
	private static List<Symbol> parseSexpr(Lexer lexer) {
		ArrayList<Symbol> result = new ArrayList<Symbol>();
		int parenLevel = 0;
		do {
			Symbol sym;
			try {
				sym = lexer.next_token();
			} catch (IOException e) {
				e.printStackTrace();
				throw new RuntimeException("Lexer couldn't read next token!");
			}
			if (sym.sym == LexerSymbols.LPAR)
				parenLevel++;
			if (sym.sym == LexerSymbols.RPAR)
				parenLevel--;
			result.add(sym);
		} while (parenLevel > 0);
		return result;
	}
}
