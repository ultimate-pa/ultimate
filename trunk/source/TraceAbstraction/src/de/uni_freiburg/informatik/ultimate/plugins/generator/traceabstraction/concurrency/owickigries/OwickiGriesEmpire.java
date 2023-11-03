package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.owickigries;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * An Owicki/Gries Empire annotation of a Petri program.
 *
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <LETTER>
 *            The type of program statements
 * @param <PLACE>
 *            The type of places in the Petri program
 */
public class OwickiGriesEmpire<LETTER, PLACE> {

	/**
	 * The set of Territories.
	 */
	/* TODO:Change type to Set<TERRITORY> */
	private final Set<Set<Set<PLACE>>> mEmpire;

	/**
	 * The set of regions in the Empire.
	 */
	/* TODO:Change type to Set<REGION> */
	private final Set<Set<PLACE>> mColony;

	/**
	 * "Law" - maps a territory to a predicate that holds at all markings contained in the territory. TODO: Change Map
	 * type to territory,predicate.
	 */
	private final Map<PLACE, IPredicate> mLaw;

	/**
	 * The annotated Petri program.
	 */
	private final IPetriNet<LETTER, PLACE> mPetriNet;

	/**
	 * The foundation crown map of the empire.
	 */
	private final Map<LETTER, PLACE> mCrown;

	/**
	 * A symbol table containing both the program symbols and the ghost variables in the annotation.
	 */
	private final IIcfgSymbolTable mSymbolTable;

	public OwickiGriesEmpire(final Set<Set<Set<PLACE>>> empire, final Set<Set<PLACE>> colony,
			final Map<PLACE, IPredicate> law, final IPetriNet<LETTER, PLACE> net, final Map<LETTER, PLACE> crown,
			final IIcfgSymbolTable symbolTable) {

		mEmpire = empire;
		mColony = colony;
		mLaw = law;
		mPetriNet = net;
		mCrown = crown;
		mSymbolTable = symbolTable;
	}

	public Set<Set<Set<PLACE>>> getEmpire() {
		return mEmpire;
	}

	public Set<Set<PLACE>> getColony() {
		return mColony;
	}

	public Map<PLACE, IPredicate> getLaw() {
		return mLaw;
	}

	public Map<LETTER, PLACE> getCrown() {
		return mCrown;
	}

	/**
	 * TODO: Check Inductivity & Interference freedom, other properties of all territories
	 */
	public boolean checkValidity() {
		return true;
	}
}
