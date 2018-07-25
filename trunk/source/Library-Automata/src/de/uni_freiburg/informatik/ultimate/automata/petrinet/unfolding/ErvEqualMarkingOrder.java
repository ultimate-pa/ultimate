package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

/**
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * 
 * @param <LETTER>
 *            Type of letters from the alphabet used to label transitions
 * @param <C>
 *            place content type
 */
public class ErvEqualMarkingOrder<LETTER, C> implements IOrder<LETTER, C> {
	
	private final IOrder<LETTER, C> mMcMillanOrder = new McMillanOrder<>();
	private final IOrder<LETTER, C> mErvOrder = new EsparzaRoemerVoglerOrder<>();
	
	@Override
	public int compare(final Event<LETTER, C> o1, final Event<LETTER, C> o2) {
		int result = mMcMillanOrder.compare(o1, o2);
		if (result != 0) {
			return result;
		}
		// TODO schaetzc 2018-07-12: Comparator returning 0 stands for equality. Is the "!" really correct?
		if (!o1.getMark().equals(o2.getMark())) {
			return 0;
		}
		final Configuration<LETTER, C> c1 = o1.getLocalConfiguration();
		final Configuration<LETTER, C> c2 = o2.getLocalConfiguration();
		result = compare(c1, c2);
		return result;
	}

	@Override
	public int compare(final Configuration<LETTER, C> c1, final Configuration<LETTER, C> c2) {
		return mErvOrder.compare(c1, c2);
	}
}
