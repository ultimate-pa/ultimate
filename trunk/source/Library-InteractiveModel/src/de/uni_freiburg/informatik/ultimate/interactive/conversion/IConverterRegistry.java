package de.uni_freiburg.informatik.ultimate.interactive.conversion;

import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

/**
 * Interface that provides a way to convert between Types.
 * 
 * @author Julian Jarecki
 *
 * @param <IA,IB>
 */
public interface IConverterRegistry<IA, IB> {
	<A extends IA> IConverter<A, ? extends IB> getAB(Class<A> typeA);

	<B extends IB> IConverter<? extends IA, B> getAB2(Class<B> typeB);

	<B extends IB, D extends IB> IResponseConverter<? extends IA, D, B> getRConv(Class<B> typeB, Class<D> typeD);

	<B extends IB> IConverter<B, ? extends IA> getBA(Class<B> typeB);

	<A extends IA> IConverter<? extends IB, A> getBA2(Class<A> typeA);

	<A extends IA, B extends IB> void registerAB(IConverter<A, B> converter);

	<A extends IA, B extends IB> void registerBA(IConverter<B, A> converter);

	<A extends IA, D extends IB, B extends IB> void registerRConv(IResponseConverter<A, D, B> responseConverter);

	default <A extends IA, D extends IB, B extends IB> void registerRConv(final Class<A> typA, final Class<D> typD,
			final Class<B> tB, final BiFunction<A, D, B> ad2b) {
		registerRConv(converter(typA, typD, tB, ad2b));
	}

	default <A extends IA, B extends IB> void registerAB(final Class<A> tA, final Class<B> typB,
			final Function<A, B> a2b) {
		registerAB(converter(tA, typB, a2b));
	}

	default <A extends IA, B extends IB> void registerBA(final Class<A> tA, final Class<B> typB,
			final Function<B, A> b2a) {
		registerBA(converter(typB, tA, b2a));
	}

	static <A, D, B> IResponseConverter<A, D, B> converter(final Class<A> typA, final Class<D> typD,
			final Class<B> typB, final BiFunction<A, D, B> ad2b) {
		return new IResponseConverter<A, D, B>() {

			@Override
			public Class<A> getTypeA() {
				return typA;
			}

			@Override
			public Class<B> getTypeB() {
				return typB;
			}

			@Override
			public Class<D> getTypeData() {
				return typD;
			}

			@Override
			public B apply(final A a, final D d) {
				return ad2b.apply(a, d);
			}
		};
	}

	static <A, B> IConverter<A, B> converter(final Class<A> typA, final Class<B> typB, final Function<A, B> a2b) {
		return new IConverter<A, B>() {

			@Override
			public Class<A> getTypeA() {
				return typA;
			}

			@Override
			public Class<B> getTypeB() {
				return typB;
			}

			@Override
			public B apply(final A a) {
				return a2b.apply(a);
			}
		};
	}

	static <A, B> IBiConverter<A, B> combine(final IBiConverter<A, B> forth, final IBiConverter<B, A> back) {
		return new IBiConverter<A, B>() {

			@Override
			public Class<A> getTypeA() {
				return forth.getTypeA();
			}

			@Override
			public Class<B> getTypeB() {
				return forth.getTypeB();
			}

			@Override
			public B apply(final A a) {
				return forth.apply(a);
			}

			@Override
			public IConverter<B, A> inverse() {
				return back;
			}
		};
	}

	public interface IResponseConverter<A, D, B> extends BiFunction<A, D, B> {
		Class<A> getTypeA();

		Class<B> getTypeB();

		Class<D> getTypeData();
	}

	public interface IConverter<A, B> extends Function<A, B> {
		Class<A> getTypeA();

		Class<B> getTypeB();

		default Consumer<A> andThen(final Consumer<B> consumer) {
			return a -> consumer.accept(apply(a));
		}

		default Supplier<B> compose(final Supplier<A> supplier) {
			return () -> apply(supplier.get());
		}
	}

	public interface IBiConverter<A, B> extends IConverter<A, B> {
		IConverter<B, A> inverse();
	}
}
