package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

/**
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * 
 * @param <LETTER>
 *            Type of letters from the alphabet used to label transitions
 * @param <PLACE>
 *            place content type
 */
public class ErvEqualMarkingOrder<LETTER, PLACE> implements IOrder<LETTER, PLACE> {
	
	private final IOrder<LETTER, PLACE> mMcMillanOrder = new McMillanOrder<>();
	private final IOrder<LETTER, PLACE> mErvOrder = new EsparzaRoemerVoglerOrder<>();
	
	@Override
	public int compare(final Event<LETTER, PLACE> o1, final Event<LETTER, PLACE> o2) {
		int result = mMcMillanOrder.compare(o1, o2);
		if (result != 0) {
			return result;
		}
		// TODO schaetzc 2018-07-12: Comparator returning 0 stands for equality. Is the "!" really correct?
		if (!o1.getMark().equals(o2.getMark())) {
			return 0;
		}
		final Configuration<LETTER, PLACE> c1 = o1.getLocalConfiguration();
		final Configuration<LETTER, PLACE> c2 = o2.getLocalConfiguration();
		result = compare(c1, c2);
		return result;
	}

	@Override
	public int compare(final Configuration<LETTER, PLACE> c1, final Configuration<LETTER, PLACE> c2) {
		return mErvOrder.compare(c1, c2);
	}
}
