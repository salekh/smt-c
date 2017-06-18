/**
 * @file TRational.h
 * @author Sanchit Alekh <sanchit.alekh@rwth-aachen.de>
 * @author Karsten Jungnitsch <karsten.jungnitsch@rwth-aachen.de>
 * @author Alexander Reeh <alexander.reeh@rwth-aachen.de>
 *
 */

#pragma once

#include "TRational.h"

namespace smtrat {

	/**************************************
				CONSTRUCTORS
	**************************************/

	TRational::TRational():
		rationalPart(0),
		deltaPart(0)
	{}

	TRational::TRational(const Rational& rational):
		rationalPart(rational),
		deltaPart(0)
	{}

	TRational::TRational(const Rational& rational, const Rational& delta):
		rationalPart(rational),
		deltaPart(delta)
	{}

	TRational::~TRational(){}

	
	/**************************************
			OVERLOAD OPERATORS
	**************************************/

	/**
	 * 
	 * @param _rational
	 * @return
	*/
	TRational& TRational::operator=(const TRational& _rational){
		rationalPart = _rational.getRationalPart();
        deltaPart = _rational.getDeltaPart();
        return *this;
	}

	/**
     * 
     * @param _rational
     * @return
    */
    TRational TRational::operator +( const TRational& _rational) const{
		Rational first = rationalPart + _rational.getRationalPart();
        Rational second = deltaPart + _rational.getDeltaPart();
        return TRational(first, second);
    }

    /**
     * 
     * @param _rational
    */
 	void TRational::operator +=( const TRational& _rational ){
 		this->rationalPart += _rational.getRationalPart();
        this->deltaPart += _rational.getDeltaPart();
 	}

	/**
     * 
     * @param _rational
     * @return
    */
    TRational TRational::operator -( const TRational& _rational) const{
		Rational first = rationalPart - _rational.getRationalPart();
        Rational second = deltaPart - _rational.getDeltaPart();
        return TRational(first, second);
    }

    /**
     * 
     * @param _rational
    */
 	void TRational::operator -=( const TRational& _rational ){
 		this->rationalPart -= _rational.getRationalPart();
        this->deltaPart -= _rational.getDeltaPart();
 	}

 	/**
     * 
     * @param _rational
     * @return
    */
    TRational TRational::operator *( const Rational& _a) const{
		Rational first = _a * rationalPart;
        Rational second = _a * deltaPart;
        return TRational(first, second);
    }

    /**
     * 
     * @param _rational
    */
 	void TRational::operator *=( const TRational& _rational ){
 		this->rationalPart *= _rational.getRationalPart();
        this->deltaPart *= _rational.getDeltaPart();
 	} 	


 	/**
     * 
     * @param _rational
     * @return
    */
    void TRational::operator *=( const Rational& _a) {
		this->rationalPart *= _a;
		this->deltaPart *= _a;
    }

	/**
     * 
     * @param _rational
     * @return
    */
 	TRational TRational::operator /( const Rational& _a) const {
		Rational first = rationalPart / _a;
        Rational second = deltaPart / _a;
        return TRational(first, second);
    }

 	/**
     * 
     * @param _rational
     * @return
    */
    void TRational::operator /=( const Rational& _a) {
		this->rationalPart *= _a;
		this->deltaPart *= _a;
    }

    bool TRational::operator <(const TRational& _rational) const {
    	if( this->rationalPart < _rational.mainPart() ) {
            return true;
        } else if( this->rationalPart == _rational.mainPart() ) {
            if( this->deltaPart < _rational.deltaPart() ) {
            	return true;
			}
        }
        return false;
    }

    bool TRational::operator <=(const TRational& _rational) const {
    	bool b = false;
        if( (this->MainPart < _rational.mainPart()) || (this->MainPart == _rational.mainPart() && this->DeltaPart <= _rational.deltaPart()) )
            b = true;
        return b;
    }

    bool TRational::operator ==(const TRational& _rational) const {
    	bool b = false;
        if((this->MainPart == _rational.mainPart() && this->DeltaPart <= _rational.deltaPart()))
            b = true;
        return b;
    }

    bool TRational::operator ==(const Rational& _a) const {
    	return (this->mainPart == _a && this->deltaPart == 0)
    }

    bool TRational::operator <(const Rational& _a) const {
    	return ((this->mainPart < _a) || (this->mainPart == _a && this->deltaPart < 0))
    }

    bool TRational::operator >(const Rational& _a) const {
    	return ((this->mainPart > _a) || (this->mainPart == _a && this->deltaPart > 0))
    }

    bool TRational::operator <=(const Rational& _a) const {
    	return ((this->mainPart < _a) || (this->mainPart == _a && this->deltaPart <= 0))
    }

    bool TRational::operator >=(const Rational& _a) const {
    	return ((this->mainPart > _a) || (this->mainPart == _a && this->deltaPart >= 0))
    }

} // smtrat


