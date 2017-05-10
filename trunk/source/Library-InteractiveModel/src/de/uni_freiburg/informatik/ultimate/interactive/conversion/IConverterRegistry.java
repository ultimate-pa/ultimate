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
	<A extends IA> IConverter<A, ? extends IB> getAB(final Class<A> typeA);

	<B extends IB> IConverter<? extends IA, B> getAB2(final Class<B> typeB);

	<B extends IB, D extends IB> IResponseConverter<? extends IA, D, B> getRConv(final Class<B> typeB,
			final Class<D> typeD);

	<B extends IB> IConverter<B, ? extends IA> getBA(final Class<B> typeB);

	<A extends IA> IConverter<? extends IB, A> getBA2(final Class<A> typeA);

	<A extends IA, B extends IB> void registerAB(IConverter<A, B> converter);

	<A extends IA, B extends IB> void registerBA(IConverter<B, A> converter);

	<A extends IA, D extends IB, B extends IB> void registerRConv(IResponseConverter<A, D, B> responseConverter);

	default <A extends IA, D extends IB, B extends IB> void registerRConv(Class<A> tA, Class<D> tD, Class<B> tB,
			BiFunction<A, D, B> ad2b) {
		registerRConv(converter(tA, tD, tB, ad2b));
	}

	default <A extends IA, B extends IB> void registerAB(Class<A> tA, Class<B> tB, Function<A, B> a2b) {
		registerAB(converter(tA, tB, a2b));
	}

	default <A extends IA, B extends IB> void registerBA(Class<A> tA, Class<B> tB, Function<B, A> b2a) {
		registerBA(converter(tB, tA, b2a));
	}

	static <A, D, B> IResponseConverter<A, D, B> converter(Class<A> tA, Class<D> tD, Class<B> tB,
			BiFunction<A, D, B> ad2b) {
		return new IResponseConverter<A, D, B>() {

			@Override
			public Class<A> getTypeA() {
				return tA;
			}

			@Override
			public Class<B> getTypeB() {
				return tB;
			}

			@Override
			public Class<D> getTypeData() {
				return tD;
			}

			@Override
			public B apply(A a, D d) {
				return ad2b.apply(a, d);
			}
		};
	}

	static <A, B> IConverter<A, B> converter(Class<A> tA, Class<B> tB, Function<A, B> a2b) {
		return new IConverter<A, B>() {

			@Override
			public Class<A> getTypeA() {
				return tA;
			}

			@Override
			public Class<B> getTypeB() {
				return tB;
			}

			@Override
			public B apply(A a) {
				return a2b.apply(a);
			}
		};
	}

	public static interface IResponseConverter<A, D, B> extends BiFunction<A, D, B> {
		Class<A> getTypeA();

		Class<B> getTypeB();

		Class<D> getTypeData();
	}

	public static interface IConverter<A, B> extends Function<A, B> {
		Class<A> getTypeA();

		Class<B> getTypeB();

		default Consumer<A> andThen(Consumer<B> consumer) {
			return a -> consumer.accept(apply(a));
		}

		default Supplier<B> compose(Supplier<A> supplier) {
			return () -> apply(supplier.get());
		}
	}

	public static interface IBiConverter<A, B> extends IConverter<A, B> {
		IConverter<B, A> inverse();
	}

	static <A, B> IBiConverter<A, B> combine(IBiConverter<A, B> forth, IBiConverter<B, A> back) {
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
			public B apply(A a) {
				return forth.apply(a);
			}

			@Override
			public IConverter<B, A> inverse() {
				return back;
			}
		};
	}
}
