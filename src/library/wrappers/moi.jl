# ~ Currently, all models in this context are unconstrained by definition.
MOI.supports_constraint(
    ::AbstractSampler,
    ::Type{<:MOI.AbstractFunction},
    ::Type{<:MOI.AbstractSet},
) = false

# ~ They are also binary
MOI.supports_constraint(
    ::AbstractSampler,
    ::Type{VI},
    ::Type{MOI.ZeroOne},
) = true

MOI.supports_constraint(
    ::AbstractSampler,
    ::Type{VI},
    ::Type{Spin},
) = true

# ~ Objective Function Support
MOI.supports(
    ::AbstractSampler,
    ::MOI.ObjectiveFunction{<:Any}
) = false

MOI.supports(
    ::AbstractSampler{T},
    ::MOI.ObjectiveFunction{<:Union{SQF{T}, SAF{T}, VI}}
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

# No constraints, no dual solutions
MOI.get(::AbstractSampler, ::MOI.DualStatus) = MOI.NO_SOLUTION

const MOI_ATTRIBUTE = Union{
    MOI.Name,
    MOI.Silent,
    MOI.TimeLimitSec,
    MOI.NumberOfThreads,
    MOI.VariablePrimalStart,
}

# ~*~ :: MathOptInterface :: ~*~ #
function MOI.empty!(sampler::AbstractSampler)
    sampler = nothing

    return sampler
end

function MOI.is_empty(sampler::AbstractSampler)
    return isnothing(sampler)
end

function MOI.optimize!(sampler::AbstractSampler)
    return _sample!(sampler)
end

function MOI.copy_to(sampler::AbstractSampler{T}, model::MOI.ModelLike) where {T}
    MOI.empty!(sampler)

    sampler = parse_model(T, model)::QUBOTools.Model{VI,T}

    ws = QUBOTools.warm_start(sampler)::Dict{VI,Int}

    # Collect warm-start values
    for v in MOI.get(model, MOI.ListOfVariableIndices())
        x = MOI.get(model, MOI.VariablePrimalStart(), v)

        MOI.set(sampler, MOI.VariablePrimalStart(), v, x)

        if !isnothing(x)
            ws[v] = QUBOTools.cast(
                source_domain(sampler) => target_domain(sampler),
                round(Int, x),
            )
        end
    end

    return MOIU.identity_index_map(model)
end

function MOI.get(
    sampler::AbstractSampler,
    st::Union{MOI.PrimalStatus,MOI.DualStatus},
    ::VI,
)
    if !(1 <= st.result_index <= MOI.get(sampler, MOI.ResultCount()))
        return MOI.NO_SOLUTION
    else
        # This status is also not very accurate, but all points are feasible
        # in a general sense since these problems are unconstrained.
        return MOI.FEASIBLE_POINT
    end
end

function MOI.get(sampler::AbstractSampler, ::MOI.RawStatusString)
    solution_metadata = QUBOTools.metadata(QUBOTools.solution(sampler))

    if !haskey(solution_metadata, "status")
        return ""
    else
        return solution_metadata["status"]::String
    end
end

MOI.supports(::AbstractSampler, ::MOI.RawStatusString) = true

function MOI.get(sampler::AbstractSampler, ::MOI.ResultCount)
    return length(QUBOTools.solution(sampler))
end

function MOI.get(sampler::AbstractSampler, ::MOI.TerminationStatus)
    ω = QUBOTools.solution(sampler)

    if isempty(ω)
        if isempty(QUBOTools.metadata(ω))
            return MOI.OPTIMIZE_NOT_CALLED
        else
            return MOI.OTHER_ERROR
        end
    else
        # This one is a little bit tricky...
        # It is nice if samplers implement this method in order to give
        # more accurate information.
        return MOI.LOCALLY_SOLVED
    end
end

function MOI.get(sampler::AbstractSampler{T}, ::MOI.ObjectiveSense) where {T}
    sense = QUBOTools.sense(sampler)

    if sense === QUBOTools.Min
        return MOI.MIN_SENSE
    else
        return MOI.MAX_SENSE
    end
end

function MOI.get(sampler::AbstractSampler, ov::MOI.ObjectiveValue)
    i = ov.result_index
    ω = QUBOTools.solution(sampler)
    m = length(ω)

    if isempty(ω)
        error("Invalid result index '$i'; There are no solutions")
    elseif !(1 <= i <= n)
        error("Invalid result index '$i'; There are $(m) solutions")
    end

    return QUBOTools.value(ω, i)
end

function MOI.get(sampler::AbstractSampler, ::MOI.SolveTimeSec)
    return QUBOTools.effective_time(QUBOTools.solution(sampler))
end

function MOI.get(sampler::AbstractSampler{T}, vp::MOI.VariablePrimal, vi::VI) where {T}
    i = vp.result_index
    ω = QUBOTools.solution(sampler)
    m = length(ω)

    if isempty(ω)
        error("Invalid result index '$i'; There are no solutions")

        return nothing
    elseif !(1 <= i <= m)
        error("Invalid result index '$i'; There are $(m) solutions")

        return nothing
    end

    j = QUBOTools.index(sampler, vi)
    s = QUBOTools.state(ω, i, j)

    return convert(T, s)
end

function MOI.get(sampler::AbstractSampler, ::MOI.NumberOfVariables)
    return QUBOTools.dimension(sampler)
end

# ~*~ File IO: Base API ~*~ #
# function Base.write(
#     filename::AbstractString,
#     sampler::AbstractSampler,
#     fmt::QUBOTools.AbstractFormat = QUBOTools.infer_format(filename),
# )
#     return QUBOTools.write_model(filename, sampler, fmt)
# end

# function Base.read!(
#     filename::AbstractString,
#     sampler::AbstractSampler,
#     fmt::QUBOTools.AbstractFormat = QUBOTools.infer_format(filename),
# )
#     sampler.source = QUBOTools.read_model(filename, fmt)
#     sampler.target = QUBOTools.format(sampler, sampler.source)

#     return sampler
# end

function warm_start(sampler::AbstractSampler, i::Integer)
    v = QUBOTools.variable_inv(sampler, i)
    x = MOI.get(sampler, MOI.VariablePrimalStart(), v)

    if isnothing(x)
        return nothing
    else
        return QUBOTools.cast(
            source_domain(sampler) => target_domain(sampler),
            round(Int, x),
        )
    end
end

function warm_start(sampler::AbstractSampler{T}) where {T}
    n = MOI.get(sampler, MOI.NumberOfVariables())
    s = sizehint!(Dict{Int,Int}(), n)

    for i = 1:n
        x = warm_start(sampler, i)
        isnothing(x) || (s[i] = x)
    end

    return s
end
