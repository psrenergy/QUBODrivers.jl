module QUBOTools.MOIWrapper

import QUBOTools

function QUBOTools.varlt(x::VI, y::VI)
    return isless(x.value, y.value)
end

function QUBOTools.sense(sense::MOI.OptimizationSense)
    if sense === MOI.MIN_SENSE
        return QUBOTools.sense(:min)
    elseif sense === MOI.MAX_SENSE
        return QUBOTools.sense(:max)
    else
        error("Invalid sense for QUBO: '$sense'")

        return nothing
    end
end

end

@doc raw"""
    Spin()

The set ``\left\lbrace{}{-1, 1}\right\rbrace{}``.
"""
struct Spin <: MOI.AbstractScalarSet end

function MOIU._to_string(options::MOIU._PrintOptions, ::Spin)
    return string(MOIU._to_string(options, ∈), " {-1, 1}")
end

function MOIU._to_string(::MOIU._PrintOptions{MIME"text/latex"}, ::Spin)
    return raw"\in \left\lbrace{}{-1, 1}\right\rbrace{}"
end

# ~ Currently, all models in this context are unconstrained by definition.
MOI.supports_constraint(
    ::AbstractSampler,
    ::Type{<:MOI.AbstractFunction},
    ::Type{<:MOI.AbstractSet},
) = false

# ~ They are also binary
MOI.supports_constraint(
    ::AbstractSampler,
    ::Type{<:MOI.VariableIndex},
    ::Type{<:MOI.ZeroOne},
) = true

MOI.supports_constraint(::AbstractSampler, ::Type{<:MOI.VariableIndex}, ::Type{<:Spin}) =
    true

# ~ Objective Function Support
MOI.supports(::AbstractSampler, ::MOI.ObjectiveFunction{<:Any}) = false

MOI.supports(
    ::AbstractSampler{T},
    ::MOI.ObjectiveFunction{<:Union{SQF{T},SAF{T},VI}},
) where {T} = true

# By default, all samplers are their own raw solvers.
MOI.get(sampler::AbstractSampler, ::MOI.RawSolver) = sampler

# Since problems are unconstrained, all available solutions are feasible.
function MOI.get(sampler::AbstractSampler, ps::MOI.PrimalStatus)
    n = MOI.get(sampler, MOI.ResultCount())
    i = ps.result_index

    if 1 <= i <= n
        return MOI.FEASIBLE_POINT
    else
        return MOI.NO_SOLUTION
    end
end

MOI.get(::AbstractSampler, ::MOI.DualStatus) = MOI.NO_SOLUTION

function reads(model; result::Integer = 1)
    return QUBOTools.reads(model, result)
end

function qubo_parse_error(msg::AbstractString)
    # Throw ToQUBO.jl advertisement on parsing error:
    error(
        """
        The current model could not be converted to QUBO in a straightforward fashion:
        - $msg

        Consider using the ToQUBO.jl package, a sophisticated reformulation framework.
            pkg> add ToQUBO # 😎
        """,
    )

    return nothing
end

@doc raw"""
    parse_model(model::MOI.ModelLike)
    parse_model(T::Type, model::MOI.ModelLike)

If the given model is ready to be interpreted as a QUBO model, then returns the corresponding `QUBOTools.StandardQUBOModel`.

A few conditions must be met:
    1. All variables must be binary of a single kind (`VI ∈ MOI.ZeroOne` or `VI ∈ Spin`)
    2. No other constraints are allowed
    3. The objective function must be of type `MOI.ScalarQuadraticFunction`, `MOI.ScalarAffineFunction` or `MOI.VariableIndex`
    4. The objective sense must be either `MOI.MIN_SENSE` or `MOI.MAX_SENSE`
"""
function parse_model end

function parse_model(model::MOI.ModelLike)
    return parse_model(Float64, model)
end

function _is_quadratic(model::MOI.ModelLike)
    return MOI.get(model, MOI.ObjectiveFunctionType()) <: Union{SQF,SAF,VI}
end

function _is_unconstrained(model::MOI.ModelLike)
    for (F, S) in MOI.get(model, MOI.ListOfConstraintTypesPresent())
        if !(F === VI && (S === MOI.ZeroOne || S === Spin))
            return false
        end
    end

    return true
end

function _is_optimization(model::MOI.ModelLike)
    S = MOI.get(model, MOI.ObjectiveSense())

    return (S === MOI.MAX_SENSE || S === MOI.MIN_SENSE)
end

function _extract_model(::Type{T}, Ω::Set{VI}, model::MOI.ModelLike, domain::QUBOTools.Domain) where {T}
    if domain === QUBOTools.BoolDomain
        return _extract_bool_model(T, Ω, model)
    elseif domain === QUBOTools.SpinDomain
        return _extract_spin_model(T, Ω, model)
    else
        error("Invalid domain '$domain'")

        return nothing
    end
end

function _extract_variable_info(model::MOI.ModelLike)
    Ω = Set{VI}(MOI.get(model, MOI.ListOfVariableIndices()))
    𝔹 = Set{VI}(
        MOI.get(model, MOI.ConstraintFunction(), ci) for
        ci in MOI.get(model, MOI.ListOfConstraintIndices{VI,MOI.ZeroOne}())
    )
    𝕊 = if MOI.supports_constraint(model, VI, Spin)
        Set{VI}(
            MOI.get(model, MOI.ConstraintFunction(), ci) for
            ci in MOI.get(model, MOI.ListOfConstraintIndices{VI,Spin}())
        )
    else # Models aren't obligated to support `Spin`!
        Set{VI}() # empty set
    end

    # Retrieve Variable Domain
    # Assuming 𝕊, 𝔹 ⊆ Ω
    if !isempty(𝕊) && !isempty(𝔹)
        qubo_parse_error("The given model contains both boolean and spin variables")
    elseif isempty(𝕊) # QUBO model?
        if 𝔹 != Ω
            qubo_parse_error("Not all variables in the given model are boolean")
        else
            return (Ω, QUBOTools.domain(:bool))
        end
    elseif isempty(𝔹) # Ising model?
        if 𝕊 != Ω
            qubo_parse_error("Not all variables in the given model are spin")
        else
            return (Ω, QUBOTools.domain(:spin))
        end
    end
    
    return nothing
end

function _extract_bool_model(::Type{T}, Ω::Set{VI}, model::MOI.ModelLike) where {T}
    L = Dict{VI,T}(xi => zero(T) for xi ∈ Ω)
    Q = Dict{Tuple{VI,VI},T}()

    offset = zero(T)

    F = MOI.get(model, MOI.ObjectiveFunctionType())
    f = MOI.get(model, MOI.ObjectiveFunction{F}())

    if F <: VI
        L[f] += one(T)
    elseif F <: SAF
        for a in f.terms
            ci = a.coefficient
            xi = a.variable

            L[xi] += ci
        end

        offset += f.constant
    elseif F <: SQF
        for a in f.affine_terms
            ci = a.coefficient
            xi = a.variable

            L[xi] += ci
        end

        for a in f.quadratic_terms
            cij = a.coefficient
            xi = a.variable_1
            xj = a.variable_2

            if xi == xj
                # ~ MOI assumes 
                #       SQF := ½ x' Q x + a' x + β
                #   Thus, the main diagonal is doubled from our point of view
                # ~ Also, in this case, x² = x
                L[xi] += cij / 2
            else
                Q[xi, xj] = get(Q, (xi, xj), zero(T)) + cij
            end
        end

        offset += f.constant
    end

    return (L, Q, offset)
end

function _extract_spin_model(::Type{T}, Ω::Set{VI}, model::MOI.ModelLike) where {T}
    L = Dict{VI,T}(xi => zero(T) for xi ∈ Ω)
    Q = Dict{Tuple{VI,VI},T}()

    offset = zero(T)

    F = MOI.get(model, MOI.ObjectiveFunctionType())
    f = MOI.get(model, MOI.ObjectiveFunction{F}())

    if F <: VI
        L[f] += one(T)
    elseif F <: SAF
        for a in f.terms
            ci = a.coefficient
            xi = a.variable

            L[xi] += ci
        end

        offset += f.constant
    elseif F <: SQF
        for a in f.affine_terms
            ci = a.coefficient
            xi = a.variable

            L[xi] += ci
        end

        for a in f.quadratic_terms
            cij = a.coefficient
            xi = a.variable_1
            xj = a.variable_2

            if xi == xj
                # ~ MOI assumes 
                #       SQF := ½ s' J s + h' s + β
                #   Thus, the main diagonal is doubled from our point of view
                # ~ Also, in this case, s² = 1
                offset += cij / 2
            else
                Q[xi, xj] = get(Q, (xi, xj), zero(T)) + cij
            end
        end

        offset += f.constant
    end

    return (L, Q, offset)
end

function parse_model(T::Type, model::MOI.ModelLike)
    # ~*~ Check for emptiness ~*~ #
    if MOI.is_empty(model)
        return QUBOTools.Model{VI,T,Int}(
            Dict{VI,T}(),
            Dict{Tuple{VI,VI},T}();
            sense  = QUBOTools.MinSense(),
            domain = QUBOTools.BoolDomain(),
        )
    end

    # ~*~ Validate Model ~*~ #
    if !_is_quadratic(model)
        qubo_parse_error("The given model's objective function is not a quadratic or linear polynomial")
    end

    if !_is_optimization(model)
        qubo_parse_error("The given model lacks an optimization sense")
    end

    if !_is_unconstrained(model)
        qubo_parse_error("The given model is not unconstrained")
    end

    Ω, domain = _extract_variable_info(model)

    # ~*~ Retrieve Model ~*~ #
    L, Q, offset = _extract_model(T, Ω, model, domain)
    scale        = one(T)

    # ~*~ Objective Sense ~*~ #
    sense = QUBOTools.sense(MOI.get(model, MOI.ObjectiveSense()))

    # ~*~ Return Model ~*~ #
    return QUBOTools.Model{VI,T,Int}(
        Ω, L, Q;
        scale  = scale,
        offset = offset,
        sense  = sense,
        domain = domain,
    )
end
