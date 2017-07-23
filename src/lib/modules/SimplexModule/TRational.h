/**
 * @file TRational.h
 * @author Sanchit Alekh <sanchit.alekh@rwth-aachen.de>
 * @author Karsten Jungnitsch <karsten.jungnitsch@rwth-aachen.de>
 * @author Alexander Reeh <alexander.reeh@rwth-aachen.de>
 *
 */

 #pragma once

#include "../../Common.h"
#include <sstream>

namespace smtrat{

	class TRational
	{

	private:
		/**
		* Rational Part (for weak inequalities)
		*/
		Rational rationalPart=0;

		/*
		* Delta Part (for strict inequalities)
		*/	
		Rational deltaPart=0;

		/*
		* Infinity part (1 = +inf, -1 = -inf, 0 != -/+ inf)
		* Is only used for comparison, not for arithmethic operations
		*/
		int infPart = 0;


	public:
		

		TRational(const Rational& rational);
		
		TRational(const Rational& rational, const Rational& delta);
		
		TRational(const Rational& rational, const Rational& delta, const int& inf);
		
		/*
		* Default constructor
		*/
		TRational();
		

		~TRational();

		/**************************************
					GETTERS
		**************************************/


		/*
		* getter for Rational Value
		* @return Rational Value
		*/
		const Rational& getRationalPart() const{
			return rationalPart;
		}

		
		/*
		* getter for Delta Value
		* @return Delta Value
		*/

		const Rational& getDeltaPart() const{
			return deltaPart;
		}

		/*
		* getter for Inf value
		*/

		const int& getInfPart() const{
			return infPart;
		}




		TRational& operator=(const TRational& _rational);


		TRational operator +( const TRational& _rational) const;


		void operator +=( const TRational& _rational );


		TRational operator -( const TRational& _rational ) const;


		void operator -=( const TRational& _rational );


		TRational operator *( const Rational& _a ) const;


		void operator *=( const TRational& _rational );

		void operator *=( const Rational& _a );


		TRational operator /( const Rational& _a ) const;


		void operator /=( const Rational& _a );


		bool operator <( const TRational& _rational ) const;
		bool operator >( const TRational& _rational ) const
		{
			return _rational < *this;
		}


		bool operator <=( const TRational& _rational ) const;
		bool operator >=( const TRational& _rational ) const
		{
			return _rational <= *this;
		}


		bool operator ==( const TRational& _rational ) const;
		bool operator !=( const TRational& _rational ) const
		{
			return !(*this == _rational);
		}


		bool operator ==( const Rational& _a ) const;
		bool operator !=( const Rational& _a ) const
		{
			return !(*this == _a);
		}


		bool operator <( const Rational& _a ) const;


		bool operator >( const Rational& _a ) const;

		bool operator <=( const Rational& _a ) const;


		bool operator >=( const Rational& _a ) const;

		
		friend std::ostream& operator<<( std::ostream& stream, const TRational& t );
	};



}
