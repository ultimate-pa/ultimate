package de.uni_freiburg.informatik.ultimate.smtinterpol.proofcheck;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.*;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 * This is the main controller to check the correctness of an SMTInterpol proof
 * by translating and transferring it to Isabelle.
 * 
 * NOTE: Quantifiers were not supported up until this implementation, so they
 * are not supported. However, the most important places that must be changed
 * to support them are marked with '<quantifiers>'
 * (ProofConverter, TermConverter, and SubstitutionConverter only). 
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 */
public class ProofChecker extends SMTInterpol {
	// name of the parsed file (needed for output)
	private final String m_fileName;
	// name of the lemma theory file
	private final String m_lemmaFileName;
	// files for the proof to be written to
	private final BufferedWriter m_file, m_lemmaFile;
	// term converter
	private TermConverter m_converter;
	// proof converter
	private ProofConverter m_proofConverter;
	// true iff Isabelle shall be invoked directly during the process 
	private final boolean m_useIsabelle;
	// true iff output file is printed in more convenient human-readable way
	private final boolean m_prettyOutput;
	// true iff fast proofs shall be printed
	private final boolean m_fastProofs;
	// true iff only the partial proof is given
	private final boolean m_partialProof;
	// set of already bound :named definitions (for more than one check-sat)
	private final HashSet<String> m_namedSet;
	// number, prefix, and map for the assertions
	private int m_assertionNumber;
	protected static final String ASSERTION_PREFIX = "smt_prm";
	private final HashMap<Term, Integer> m_assertion2index;
	protected static final String m_partialAnnotation = ":named";
	
	/**
	 * @param fileName name of the parsed file
	 * @param useIsabelle true iff Isabelle shall be invoked as well
	 * @param prettyOutput true iff output file shall be 
	 */
	public ProofChecker(final String fileName, final boolean useIsabelle,
			final boolean prettyOutput, final boolean fastProofs,
			final boolean partialProof) {
		super();
		
		// write Isabelle files
		m_fileName = fileName;
		m_lemmaFileName = fileName + "_lemma";
		try {
			final File isaFile = createIsabelleFile();
			m_file = new BufferedWriter(new FileWriter(isaFile));
			final File lemmaFile = createTheoryFile();
			m_lemmaFile = new BufferedWriter(new FileWriter(lemmaFile));
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
		
		m_useIsabelle = useIsabelle;
		m_prettyOutput = prettyOutput;
		m_fastProofs = fastProofs;
		m_partialProof = partialProof;
		m_namedSet = new HashSet<String>();
		m_assertionNumber = 0;
		m_assertion2index = m_partialProof
				? null
				: new HashMap<Term, Integer>();
		
		// set proof producing options (never overwritten)
		if (m_partialProof) {
			super.setOption(":produce-interpolants", true);
			super.setOption(":produce-proofs", false);
		}
		else {
			super.setOption(":produce-proofs", true);
		}
		
		super.setOption(":interactive-mode", true);
	}
	
	/**
	 * {@inheritDoc}
	 * 
	 * The method is overwritten to prohibit change of proof production.
	 */
	@Override
	public void setOption(String opt, Object value)
			throws UnsupportedOperationException, SMTLIBException {
		if ((opt.equals(":produce-proofs")) ||
			(opt.equals(":interactive-mode")) ||
			(opt.equals(":produce-interpolants"))) {
			return;
		}
		
		super.setOption(opt, value);
	}
	
	/**
	 * NOTE: Setting the logics more than once messes up the Isabelle files.
	 */
	@Override
	public void setLogic(Logics logic) {
		super.setLogic(logic);
		
		// write Isabelle header
		try {
			// import linear arithmetic theory only when necessary
			final String imports;
			switch (logic) {
				case AUFLIA:
				case AUFNIRA:
				case AUFLIRA:
				case LRA:
				case QF_AUFLIA:
				case QF_LIA:
				case QF_LRA:
				case QF_NIA:
				case QF_NRA:
				case QF_UFLIA:
				case QF_UFLIRA:
				case QF_UFLRA:
				case QF_UFNRA:
				case UFLRA:
				case UFNIA:
					imports = "XLinearArithmetic";
					break;
				default:
					imports = "XBool";
			}
			
			// main file
			m_file.append("theory SMTTheory\nimports ");
			m_file.append(imports);
			m_file.append(" ");
			m_file.append(m_lemmaFileName);
			m_file.append("\nbegin\n");
			
			// lemma file
			m_lemmaFile.append("theory ");
			m_lemmaFile.append(m_lemmaFileName);
			m_lemmaFile.append("\nimports ");
			m_lemmaFile.append(imports);
			m_lemmaFile.append("\nbegin\n");
		}
		catch (IOException e) {
			throw new RuntimeException(e);
		}
		
		// set up the term converter
		m_converter = new TermConverter(m_file, logic, m_prettyOutput);
		m_proofConverter = new ProofConverter(m_file, super.getTheory(),
				m_prettyOutput, m_converter, m_fastProofs, m_partialProof,
				m_lemmaFile);
	}
	
	@Override
	public void defineFun(String fun, TermVariable[] params, Sort resultSort,
			Term definition) throws SMTLIBException {
		super.defineFun(fun, params, resultSort, definition);
		
		assert (m_converter != null);
		final String name = m_converter.toCompatibleString(fun);
		final String arrow = m_prettyOutput ? "\\<Rightarrow>" : "=>";
		
		try {
			m_lemmaFile.append("\ndefinition ");
			m_lemmaFile.append(name);
			m_lemmaFile.append("::\"");
			for (int i = 0; i < params.length; ++i) {
				m_lemmaFile.append(m_converter.getSingleSortString(
						params[i].getDeclaredSort()));
				m_lemmaFile.append(arrow);
			}
			m_lemmaFile.append(
					m_converter.getSingleSortString(resultSort));
			m_lemmaFile.append("\" where ");
			m_lemmaFile.append(name);
			m_lemmaFile.append("_def:\"");
			m_lemmaFile.append(name);
			m_lemmaFile.append(" == ");
			if (params.length > 0) {
				String append = "%";
				for (int i = 0; i < params.length; ++i) {
					m_lemmaFile.append(append);
					append = " ";
					m_converter.convertToAppendable(params[i], m_lemmaFile);
				}
				m_lemmaFile.append(". ");
			}
			m_converter.convertToAppendable(definition, m_lemmaFile);
			m_lemmaFile.append("\"\n");
		}
		catch (IOException e) {
			throw new RuntimeException(e);
		}
	}
	
	/**
	 * {@inheritDoc}
	 * 
	 * The term must be recognized later in @asserted proof nodes
	 * In the extended proof mode, the term is put in a hash map.
	 * In the partial proof mode the term is annotated with a unique string,
	 * since it may change.
	 */
	@Override
	public LBool assertTerm(Term term) throws SMTLIBException,
			UnsupportedOperationException {
		if (m_partialProof) {
			if (term instanceof AnnotatedTerm) {
				AnnotatedTerm aTerm = (AnnotatedTerm)term;
				// unpack :named annotation and pack it into a new one
				if ((aTerm.getAnnotations().length == 1) &&
					(aTerm.getAnnotations()[0].getKey().
							equals(m_partialAnnotation))) {
					term = (aTerm).getSubterm();
				}
			}
			return super.assertTerm(annotate(term,
					new Annotation(m_partialAnnotation, ASSERTION_PREFIX +
							++m_assertionNumber)));
		}
		m_assertion2index.put(new FormulaUnLet().unlet(term),
				++m_assertionNumber);
		return super.assertTerm(term);
	}
	
	/**
	 * {@inheritDoc}
	 * 
	 * The method is overwritten to extract the proof.
	 * Both the theorem and the proof are translated into a form Isabelle
	 * understands and then Isabelle checks the proof.
	 */
	@Override
	public LBool checkSat() throws SMTLIBException {
		LBool result = super.checkSat();
		
		// write unsatisfiability proof
		if (result == LBool.UNSAT) {
			final Term proof = super.getProof();
			
			try {
				// convert theorem and proof to a form Isabelle understands
				convertTheorem();
				m_proofConverter.convert(proof, m_assertion2index);
			} catch (IOException e) {
				e.printStackTrace();
				
				// close the writer before returning
				try {
					m_file.close();
					m_lemmaFile.close();
				} catch (IOException eWriter) {
					eWriter.printStackTrace();
				}
			}
		}
		
		return result;
	}
	
	@Override
	public void exit() {
		// write last line and close files
		try {
			m_file.append("\nend");
			m_file.close();
			
			m_lemmaFile.append("\nend");
			m_lemmaFile.close();
			
			// call Isabelle on the proof file
			if (m_useIsabelle) {
				callIsabelle(createIsabelleFile().getName());
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		super.exit();
	}
	
	/**
	 * This method adds a function declaration to the lemma file.
	 * 
	 * @param fun the function name
	 * @param paramSorts the parameter sorts
	 * @param resultSort the result sort
	 * @param lineFeed true iff a line feed should be printed
	 */
	private void declareConst(final String fun, final Sort[] paramSorts,
			final Sort resultSort, final boolean lineFeed) {
		assert (m_converter != null);
		final String name = m_converter.toCompatibleString(fun);
		final String arrow = m_prettyOutput ? "\\<Rightarrow>" : "=>";
		
		try {
			m_lemmaFile.append("consts ");
			m_lemmaFile.append(name);
			m_lemmaFile.append("::\"");
			for (int i = 0; i < paramSorts.length; ++i) {
				m_lemmaFile.append(
						m_converter.getSingleSortString(paramSorts[i]));
				m_lemmaFile.append(arrow);
			}
			m_lemmaFile.append(
					m_converter.getSingleSortString(resultSort));
			if (lineFeed) {
				m_lemmaFile.append("\"\n");
			}
			else {
				m_lemmaFile.append("\"");
			}
		}
		catch (IOException e) {
			throw new RuntimeException(e);
		}
	}
	
	/**
	 * This method converts an SMT-LIB theorem to an Isabelle theorem.
	 * The SMT-LIB theorem is given in the form of asserted formulae.
	 * 
	 * @throws IOException thrown by appendable
	 */
	public void convertTheorem() throws IOException {
		// theorem
		m_file.append("\ntheorem\n");
		
		// antecedents
		m_file.append("assumes ");
		String append = "";
		if (m_partialProof) {
			for (Term term : super.getAssertions()) {
				m_file.append(append);
				append = "and ";
				
				// give the premise a name
				assert (term instanceof AnnotatedTerm);
				AnnotatedTerm aTerm = (AnnotatedTerm)term;
				Annotation[] annotations = aTerm.getAnnotations();
				assert (annotations.length == 1);
				assert (annotations[0].getKey().equals(m_partialAnnotation));
				
				m_file.append(annotations[0].getValue().toString());
				m_file.append(": \"");
				
				final LinkedList<NamedWrapper> namedFuns =
						m_converter.convertAssertion(aTerm.getSubterm());
				// add functions bound by :named annotation
				for (NamedWrapper wrapper : namedFuns) {
					addNamedBond(wrapper);
				}
				
				m_file.append("\"\n");
			}
		}
		else {
			assert (m_assertion2index.size() <= super.getAssertions().length);
			for (Entry<Term, Integer> entry : m_assertion2index.entrySet()) {
				m_file.append(append);
				append = "and ";
				
				m_file.append(ASSERTION_PREFIX);
				m_file.append(Integer.toString(entry.getValue()));
				m_file.append(": \"");
				
				final LinkedList<NamedWrapper> namedFuns =
						m_converter.convertAssertion(entry.getKey());
				// add functions bound by :named annotation
				for (NamedWrapper wrapper : namedFuns) {
					addNamedBond(wrapper);
				}
				
				m_file.append("\"\n");
			}
		}
		
		// consequent
		m_file.append("shows \"False\"\n");
	}
	
	/**
	 * This method adds a function definition via the :named annotation
	 * to the Isabelle lemma file.
	 * 
	 * @param wrapper function wrapper
	 */
	private void addNamedBond(final NamedWrapper wrapper) {
		// ignore already defined terms
		if (! m_namedSet.add(wrapper.m_name)) {
			return;
		}
		
		// constant declaration
		declareConst(wrapper.m_name, new Sort[0],
				wrapper.m_subterm.getSort(), false);
		
		// constant definition
		assert (m_converter != null);
		final String name = m_converter.toCompatibleString(wrapper.m_name);
		
		try {
			m_lemmaFile.append(" defs ");
			m_lemmaFile.append(name);
			m_lemmaFile.append("_def: \"");
			m_lemmaFile.append(name);
			m_lemmaFile.append(" == ");
			m_converter.convertWithTypes(wrapper.m_subterm, m_lemmaFile);
			m_lemmaFile.append("\"\n");
		}
		catch (IOException e) {
			throw new RuntimeException(e);
		}
	}
	
	/**
	 * This method creates a file for Isabelle to the disc.
	 * 
	 * @return empty file
	 * @throws IOException thrown iff creation fails
	 */
	private File createIsabelleFile() throws IOException {
		return new File(m_fileName + ".thy");
	}
	
	/**
	 * This method creates a file for the lemmata to the disc.
	 * 
	 * @return empty file
	 * @throws IOException thrown iff creation fails
	 */
	private File createTheoryFile() throws IOException {
		return new File(m_lemmaFileName + ".thy");
	}
	
	/**
	 * This method calls Isabelle on the written proof file and receives the
	 * result (which is: has Isabelle accepted the proof or not).
	 * 
	 * @param filename the file name
	 * @throws IOException thrown iff reading Isabelle output fails
	 */
	private void callIsabelle(String filename) throws IOException {
		Runtime.getRuntime().exec(new String[]{"isabelle", "emacs", filename});
	}
}