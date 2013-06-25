_idris() {
    local cur prev words opts LIBRARIES TARGETS
    _init_completion || return

    opts=$(_parse_help "$1")
    LIBRARIES="effects"
    TARGETS="C Java bytecode javascript node"

    case "${prev}" in
        -o)
            _filedir
        ;;
        -i|--ibcsubdir)
            _filedir -d
        ;;
        -p)
            COMPREPLY=( $(compgen -W "${LIBRARIES}" -- ${cur}))
        ;;
        --target)
            COMPREPLY=( $(compgen -W "${TARGETS}" -- ${cur}))
        ;;
    esac

    if [[ $cur == -* ]]; then
        COMPREPLY=($(compgen -W "${opts}" -- ${cur}))
        return
    fi

    _filedir '@(idr)'
} &&
complete -o default -F _idris idris
