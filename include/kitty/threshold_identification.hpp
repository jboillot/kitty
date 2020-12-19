/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author CS-472 2020 Fall students
*/

#pragma once

#include <vector>
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "traits.hpp"
#include "operations.hpp"
#include "isop.hpp"

namespace kitty
{

/**
     * Check if the truth table is unate in a specific variable and, in this case, force its positivity and return true. Otherwise, return false.
     * @tparam TT
     * @param tt
     * @param var_index
     * @return
     */
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool force_positive_unate_in_variable( TT& tt, uint32_t var_index, std::vector<bool>& inverted )
{
  assert( var_index <= UINT8_MAX );
  const TT& cof0 = cofactor0( tt, (uint8_t)var_index );
  const TT& cof1 = cofactor1( tt, (uint8_t)var_index );

  if ( binary_predicate( cof1, cof0, std::greater_equal<>() ) )
  {
    inverted[var_index] = false;
    return true;
  }
  else if ( binary_predicate( cof1, cof0, std::less_equal<>() ) )
  {
    flip_inplace( tt, (uint8_t)var_index );
    inverted[var_index] = true;
    return true;
  }
  return false;
}

template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool force_positive_unate( TT& tt, std::vector<bool>& inverted )
{
  for ( uint32_t i = 0; i < tt.num_vars(); ++i )
  {
    if ( !force_positive_unate_in_variable( tt, i, inverted ) )
      return false;
  }
  return true;
}

/*! \brief Threshold logic function identification

  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].

  \param tt The truth table
  \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
             The linear form has `tt.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold( const TT& tt, std::vector<int64_t>* plf = nullptr )
{
  std::vector<int64_t> linear_form;
  std::vector<bool> inverted( tt.num_vars() );

  TT mutableTT = tt;

  /* if tt is non-TF: */
  if ( !force_positive_unate( mutableTT, inverted ) )
    return false;

  /* if tt is TF: */
  /* push the weight and threshold values into `linear_form` */
  lprec* lp( make_lp( 0, mutableTT.num_vars() + 1 ) );
  set_verbose( lp, 0 );

  set_minim( lp );

  // set the objective
  std::vector<REAL> objective( mutableTT.num_vars() + 2, 0. );
  for ( uint32_t i = 0; i <= mutableTT.num_vars(); ++i )
  {
    objective[i] = 1.;
  }
  set_obj_fn( lp, objective.data() );

  // on-set constraints
  for ( cube& on_elem : isop( mutableTT ) )
  {
    std::vector<REAL> constraint( mutableTT.num_vars() + 2, 0. );
    for ( uint32_t i = 0; i < mutableTT.num_vars(); ++i )
    {
      if ( on_elem.get_mask( i ) && on_elem.get_bit( i ) )
      {
        constraint[i + 1] = 1.;
      }
    }
    constraint[mutableTT.num_vars() + 1] = -1.;
    add_constraint( lp, constraint.data(), GE, 0. );
  }

  // off-set constraints
  for ( cube& off_elem : isop( ~mutableTT ) )
  {
    std::vector<REAL> constraint( mutableTT.num_vars() + 2, 0. );
    for ( uint32_t i = 0; i < mutableTT.num_vars(); ++i )
    {
      if ( !off_elem.get_mask( i ) || ( off_elem.get_mask( i ) && off_elem.get_bit( i ) ) )
      {
        constraint[i + 1] = 1.;
      }
    }
    constraint[mutableTT.num_vars() + 1] = -1.;
    add_constraint( lp, constraint.data(), LE, -1. );
  }

  // positivity constraints
  for ( uint32_t i = 0; i <= mutableTT.num_vars(); ++i )
  {
    std::vector<REAL> constraint( mutableTT.num_vars() + 2, 0. );
    constraint[i + 1] = 1.;
    add_constraint( lp, constraint.data(), GE, 0. );
  }

  // ILP constraints
  for ( uint32_t i = 0; i <= mutableTT.num_vars(); ++i )
  {
    set_int( lp, i, true );
  }

  int status = solve( lp );
  std::vector<REAL> lp_result( get_Ncolumns( lp ) );
  get_variables( lp, lp_result.data() );
  delete_lp( lp );
  linear_form.insert( linear_form.begin(), lp_result.begin(), lp_result.end() );

  if ( status )
    return false;

  for ( uint32_t i = 0; i < mutableTT.num_vars(); ++i )
  {
    if ( inverted[i] )
    {
      linear_form[i] *= -1.;
      linear_form[mutableTT.num_vars()] += linear_form[i];
    }
  }

  if ( plf )
  {
    *plf = linear_form;
  }
  return true;
}

} /* namespace kitty */
