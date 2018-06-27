package de.uni_freiburg.informatik.ultimate.logic;

/**
 * Empty interface that can be used to mark subclasses of {@link Script} that cannot answer check-sat queries. (E.g.
 * classes that are only used for building {@link Term}s during parsing.)
 * <p>
 * Note that this class is a symptom of an architectural problem: Some subclasses of Script are used as an interface to
 *  an actual SMT solver ({@link SMTInterpol}, {@link Scriptor}), other subclasses are used only for parsing and
 *  building {@link Term}s).
 * Once the Script class is split according to these functionalities, this interface should become obsolete.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
public interface INonSolverScript {

}
